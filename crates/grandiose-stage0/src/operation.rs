//! Request-scoped cancellation, resource accounting, and publication guards.
//!
//! These values are deliberately compiler-owned. They make hostile inputs and
//! obsolete IDE work bounded without turning limits or cancellation into
//! ambient process configuration.

use std::sync::{
    Arc,
    atomic::{AtomicBool, AtomicU64, Ordering},
};

#[derive(Clone, Debug, Default)]
pub struct CancellationToken(Arc<AtomicBool>);

impl CancellationToken {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }

    pub fn check(&self) -> Result<(), Cancelled> {
        (!self.is_cancelled()).then_some(()).ok_or(Cancelled)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Cancelled;

#[derive(Clone, Debug)]
pub struct Budget {
    name: &'static str,
    ceiling: u64,
    spent: Arc<AtomicU64>,
    parent: Option<Arc<Budget>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BudgetError {
    pub name: &'static str,
    pub ceiling: u64,
    pub requested: u64,
}

/// A bounded reservation against one request-owned budget. It is affine: the
/// reservation returns automatically on every early return, error, or
/// cancellation path, so request work accounting cannot outlive its session.
#[derive(Debug)]
pub struct BudgetLease {
    budget: Arc<Budget>,
    amount: u64,
}

impl Budget {
    pub fn root(name: &'static str, ceiling: u64) -> Arc<Self> {
        Arc::new(Self {
            name,
            ceiling,
            spent: Arc::new(AtomicU64::new(0)),
            parent: None,
        })
    }

    pub fn child(self: &Arc<Self>, name: &'static str, ceiling: u64) -> Arc<Self> {
        Arc::new(Self {
            name,
            ceiling,
            spent: Arc::new(AtomicU64::new(0)),
            parent: Some(self.clone()),
        })
    }

    /// The maximum cumulative work this budget may admit.  Callers use this
    /// when issuing a child whose independent limit is intentionally no
    /// broader than its owning phase.  The parent is still charged on every
    /// child checkpoint, so a stale observation of this value can never let a
    /// sibling overspend the request.
    pub fn ceiling(&self) -> u64 {
        self.ceiling
    }

    pub fn spent(&self) -> u64 {
        self.spent.load(Ordering::Acquire)
    }

    pub fn charge(&self, amount: u64) -> Result<(), BudgetError> {
        if let Some(parent) = &self.parent {
            parent.charge(amount)?;
        }
        if let Err(error) = self.reserve_local(amount) {
            if let Some(parent) = &self.parent {
                parent.release(amount);
            }
            return Err(error);
        }
        Ok(())
    }

    pub fn lease(self: &Arc<Self>, amount: u64) -> Result<BudgetLease, BudgetError> {
        self.charge(amount)?;
        Ok(BudgetLease {
            budget: self.clone(),
            amount,
        })
    }

    pub fn release(&self, amount: u64) {
        let previous = self.spent.fetch_sub(amount, Ordering::AcqRel);
        assert!(previous >= amount, "budget release exceeded charged amount");
        if let Some(parent) = &self.parent {
            parent.release(amount);
        }
    }

    fn reserve_local(&self, amount: u64) -> Result<(), BudgetError> {
        let mut current = self.spent.load(Ordering::Acquire);
        loop {
            let Some(next) = current.checked_add(amount) else {
                return Err(BudgetError {
                    name: self.name,
                    ceiling: self.ceiling,
                    requested: amount,
                });
            };
            if next > self.ceiling {
                return Err(BudgetError {
                    name: self.name,
                    ceiling: self.ceiling,
                    requested: amount,
                });
            }
            match self.spent.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return Ok(()),
                Err(observed) => current = observed,
            }
        }
    }
}

impl Drop for BudgetLease {
    fn drop(&mut self) {
        self.budget.release(self.amount);
    }
}

/// Stages one request-level product. The only success path checks cancellation
/// immediately before publication; dropped guards silently discard their value,
/// making partial diagnostics, interfaces, artifacts, and cache writes
/// unrepresentable through this API.
#[derive(Debug)]
pub struct PublicationGuard<T>(Option<T>);

impl<T> PublicationGuard<T> {
    pub fn stage(value: T) -> Self {
        Self(Some(value))
    }

    pub fn commit(mut self, cancellation: &CancellationToken) -> Result<T, Cancelled> {
        cancellation.check()?;
        Ok(self
            .0
            .take()
            .expect("publication guard has one staged value"))
    }

    pub fn discard(mut self) {
        self.0.take();
    }
}
