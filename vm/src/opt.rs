//! Rewriting a program's bytecode when it is loaded, before any engine runs
//! it.
//!
//! The language makes control flow out of calls: `if` is a function given
//! two blocks, and a block is a closure. So the code as compiled makes a
//! closure for every function it calls, and calls a handful of small
//! functions for every `if`. Three things are done about that, all of them
//! where the function called can be read off the code:
//!
//! - a call of a known function does not go through a closure;
//! - a function that is one computation is done in place of the call;
//! - a call that is the last thing a function does is replaced by the code
//!   of the function called, when that is small. Blocks passed to it are then
//!   known in turn, and what is left of a chain of `if` and `else` is often
//!   tests and jumps.
//!
//! A closure nothing uses any more is then not made.
//!
//! Locals are numbered by position: an instruction that gives a value gives
//! it the next number. Every rewriting here keeps that: an instruction is
//! replaced by one that gives as many values, and code written in place goes
//! at the end of the function, numbered from where it is jumped to.
//!
//! None of this is proved. It is checked by running every test program with
//! and without it (`--no-opt`).

use super::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// The most instructions a function is let grow to.
const LIMIT: usize = 800;
/// The largest function whose code is written in place of a call.
const CALLEE: usize = 40;
/// How deep code written in place may nest.
const DEPTH: usize = 16;

/// The most instructions of what follows a call that are written again for
/// each way the function called comes back.
const FOLLOW: usize = 40;

/// What a local is known to hold.
#[derive(Clone)]
enum Known {
    /// A closure of a function, with what it captured.
    Clo(usize, Vec<Atom>),
    /// A value built by a constructor from these.
    Ctor(u64, Vec<Atom>),
}

/// What follows a call whose function is written in place: the rest of the
/// clause the call was in, to be written again wherever that function gives
/// back a value.
struct Follow {
    /// The rest of the clause, as it was read, down to what ends it.
    code: Vec<Instr>,
    /// The local the call's result is, in that code's numbering.
    base: usize,
    /// The functions being written in place where the call was.
    chain: Vec<usize>,
    /// What follows the clause's own result, if it too is written in place.
    next: Option<Rc<Follow>>,
}

impl Follow {
    /// How many instructions giving back one value here leads to.
    fn weight(&self) -> usize {
        self.code.len() + 2 + self.next.as_ref().map_or(0, |n| n.weight())
    }
}

fn untake(code: &mut [Instr]) {
    for instr in code {
        for a in instr.atoms_mut() {
            if let Atom::Take(i) = *a {
                *a = Atom::Var(i);
            }
        }
    }
}

/// Does the instruction give a value, which is then the next local?
fn pushes(instr: &Instr) -> bool {
    !instr.last() && instr.fail().is_none() && !matches!(instr, Instr::Jump(_))
}

/// The instruction with its locals numbered from `base` and its places in
/// the code moved by `shift`.
fn moved(instr: &Instr, base: usize, shift: usize) -> Instr {
    let mut out = instr.clone();
    for a in out.atoms_mut() {
        if let Atom::Var(i) | Atom::Take(i) = a {
            *i += base;
        }
    }
    match &mut out {
        Instr::Op(Rhs::Place(pl)) => pl.var += base,
        Instr::TestCtor(pl, _, _, fail) | Instr::TestInt(pl, _, fail) => {
            pl.var += base;
            *fail += shift;
        }
        Instr::Jump(t) => *t += shift,
        _ => {}
    }
    out
}

/// Whether every test of the code is made before anything is pushed, so that
/// each clause starts with the locals the function starts with.
fn clauses_start_bare(code: &[Instr]) -> bool {
    let mut pushed = 0usize;
    let mut starts: HashSet<usize> = HashSet::new();
    for (pc, instr) in code.iter().enumerate() {
        if starts.contains(&pc) {
            pushed = 0;
        }
        if let Some(fail) = instr.fail() {
            if pushed != 0 || fail <= pc {
                return false;
            }
            starts.insert(fail);
        }
        if matches!(instr, Instr::Jump(_) | Instr::CallFn(..) | Instr::TailFn(..)) {
            return false;
        }
        if pushes(instr) {
            pushed += 1;
        }
        if instr.last() {
            pushed = 0;
        }
    }
    true
}

struct Opt<'a> {
    /// The functions as they were read, with no moves marked.
    codes: &'a [Vec<Instr>],
    starts: &'a [Option<usize>],
    bare: &'a [bool],
    out: Vec<Instr>,
}

impl Opt<'_> {
    /// A function that is one computation of its arguments, given back, or
    /// that gives back one of them.
    fn leaf(&self, f: usize, given: &[Atom]) -> Option<Instr> {
        let code = &self.codes[f];
        if self.starts[f] != Some(given.len()) {
            return None;
        }
        let rhs = match code.as_slice() {
            [Instr::Op(rhs), Instr::Ret(Atom::Var(r))] if *r == given.len() => rhs.clone(),
            [Instr::Ret(a)] => Rhs::Atom(a.clone()),
            _ => return None,
        };
        let mut op = Instr::Op(rhs);
        if let Instr::Op(Rhs::Place(pl)) = &mut op {
            match given.get(pl.var)? {
                Atom::Var(x) => pl.var = *x,
                _ => return None,
            }
        }
        for a in op.atoms_mut() {
            if let Atom::Var(i) = *a {
                *a = given.get(i)?.clone();
            }
        }
        Some(op)
    }

    /// May the code of `f` be written in place of a call given `given`
    /// values, with `follow` to be written after each way it comes back?
    fn can_inline(&self, f: usize, given: usize, chain: &[usize], follow: usize) -> bool {
        let code = &self.codes[f];
        let ends = code.iter().filter(|i| i.last()).count();
        code.len() <= CALLEE
            && self.bare[f]
            && self.starts[f] == Some(given)
            && !chain.contains(&f)
            && chain.len() < DEPTH
            && self.out.len() + code.len() + given + ends * follow < LIMIT
    }

    /// Write the code of `f` at the end, its locals numbered from `h`, where
    /// the values `given` are put first. Gives where it starts.
    fn inline(
        &mut self,
        f: usize,
        given: &[Atom],
        h: usize,
        known: &HashMap<usize, Known>,
        chain: &[usize],
        follow: Option<Rc<Follow>>,
    ) -> usize {
        let at = self.out.len();
        let mut inner = known.clone();
        for (k, a) in given.iter().enumerate() {
            if let Atom::Var(x) = a {
                if let Some(what) = known.get(x).cloned() {
                    inner.insert(h + k, what);
                }
            }
            self.out.push(Instr::Op(Rhs::Atom(a.clone())));
        }
        let body = self.out.len();
        let code = &self.codes[f];
        self.out.extend(code.iter().map(|i| moved(i, h, body)));
        let end = self.out.len();
        // Where a test that fails in its last clause goes: not into what is
        // written next.
        self.out.push(Instr::Stuck);
        let mut chain = chain.to_vec();
        chain.push(f);
        self.region(body, end, h + given.len(), &inner, &chain, follow);
        at
    }

    /// Write what follows a call at the end, for a result that is local `h`
    /// once `first` has run. Gives where it starts.
    fn resume(
        &mut self,
        first: Instr,
        h: usize,
        known: &HashMap<usize, Known>,
        follow: &Rc<Follow>,
    ) -> usize {
        let at = self.out.len();
        let mut inner = known.clone();
        if let Instr::Op(Rhs::Atom(Atom::Var(x))) = &first {
            if let Some(what) = known.get(x).cloned() {
                inner.insert(h, what);
            }
        }
        // A call is looked at again where it now is; anything else is done.
        let from = if matches!(first, Instr::Call(..)) { at } else { at + 1 };
        self.out.push(first);
        let base = follow.base;
        for instr in &follow.code {
            let mut i = instr.clone();
            let renumber = |x: &mut usize| {
                if *x >= base {
                    *x = *x - base + h;
                }
            };
            for a in i.atoms_mut() {
                if let Atom::Var(x) | Atom::Take(x) = a {
                    renumber(x);
                }
            }
            if let Instr::Op(Rhs::Place(pl)) = &mut i {
                renumber(&mut pl.var);
            }
            self.out.push(i);
        }
        let end = self.out.len();
        let start = if from == at { h } else { h + 1 };
        self.region(from, end, start, &inner, &follow.chain.clone(), follow.next.clone());
        at
    }

    /// Rewrite the clauses in `out[from..to]`, which start with `start`
    /// locals. `outer` is what is known of the locals there are before them,
    /// `chain` the functions whose code this is inside, and `follow` what is
    /// to happen with what the clauses give back, if that is not to give it
    /// back.
    fn region(
        &mut self,
        from: usize,
        to: usize,
        start: usize,
        outer: &HashMap<usize, Known>,
        chain: &[usize],
        follow: Option<Rc<Follow>>,
    ) {
        let heads: HashSet<usize> = (from..to).filter_map(|pc| self.out[pc].fail()).collect();
        let mut known = outer.clone();
        let mut h = start;
        // Nothing runs between what ends a clause and the next clause.
        let mut dead = false;
        for pc in from..to {
            if heads.contains(&pc) {
                known = outer.clone();
                h = start;
                dead = false;
            }
            if dead {
                continue;
            }
            let instr = self.out[pc].clone();
            // The rest of the clause: what follows a call made here.
            let rest = |out: &[Instr]| -> Option<Vec<Instr>> {
                let end = (pc + 1..to).find(|&q| out[q].last())?;
                (end - pc <= FOLLOW).then(|| out[pc + 1..=end].to_vec())
            };
            let weight = follow.as_ref().map_or(0, |k| k.weight());
            match &instr {
                Instr::Op(Rhs::Closure(f, caps)) => {
                    known.insert(h, Known::Clo(*f, caps.clone()));
                }
                Instr::Op(Rhs::Construct(tag, fields)) => {
                    known.insert(h, Known::Ctor(*tag, fields.clone()));
                }
                Instr::Op(Rhs::Rebind(Atom::Var(i), g)) => {
                    if let Some(Known::Clo(_, caps)) = known.get(i).cloned() {
                        known.insert(h, Known::Clo(*g, caps));
                    }
                }
                Instr::Op(Rhs::Atom(Atom::Var(i))) => {
                    if let Some(k) = known.get(i).cloned() {
                        known.insert(h, k);
                    }
                }
                Instr::Op(Rhs::Place(Place { var, path })) if path.len() == 1 => {
                    // A field of what was built here is what it was built from.
                    if let Some(Known::Ctor(_, fields)) = known.get(var) {
                        if let Some(field) = fields.get(path[0]).cloned() {
                            if let Atom::Var(x) = &field {
                                if let Some(k) = known.get(x).cloned() {
                                    known.insert(h, k);
                                }
                            }
                            self.out[pc] = Instr::Op(Rhs::Atom(field));
                        }
                    }
                }
                Instr::TestCtor(Place { var, path }, tag, arity, fail) if path.is_empty() => {
                    // Which constructor built what was built here is known.
                    if let Some(Known::Ctor(built, fields)) = known.get(var) {
                        if built == tag && fields.len() == *arity {
                            self.out[pc] = Instr::Jump(pc + 1);
                        } else {
                            self.out[pc] = Instr::Jump(*fail);
                            dead = true;
                        }
                    }
                }
                Instr::Ret(a) => {
                    if let Some(k) = &follow {
                        let at = self.resume(Instr::Op(Rhs::Atom(a.clone())), h, &known, k);
                        self.out[pc] = Instr::Jump(at);
                    }
                }
                Instr::Call(Atom::Var(i), args) | Instr::Tail(Atom::Var(i), args) => {
                    // What is given back at once is as good as called last.
                    let returned = matches!(self.out.get(pc + 1), Some(Instr::Ret(Atom::Var(r))) if *r == h)
                        && pc + 1 < to
                        && !heads.contains(&(pc + 1));
                    let last = matches!(instr, Instr::Tail(..));
                    let target = match known.get(i).cloned() {
                        Some(Known::Clo(f, caps)) => {
                            Some((f, args.iter().chain(caps.iter()).cloned().collect::<Vec<Atom>>()))
                        }
                        _ => None,
                    };
                    match target {
                        Some((f, given)) if last || returned => {
                            if self.can_inline(f, given.len(), chain, weight) {
                                let at = self.inline(f, &given, h, &known, chain, follow.clone());
                                self.out[pc] = Instr::Jump(at);
                                dead = true;
                            } else if let Some(k) = &follow {
                                if last {
                                    let at = self.resume(Instr::CallFn(f, given), h, &known, k);
                                    self.out[pc] = Instr::Jump(at);
                                    dead = true;
                                } else {
                                    self.out[pc] = Instr::CallFn(f, given);
                                }
                            } else {
                                self.out[pc] = Instr::TailFn(f, given);
                                dead = true;
                            }
                        }
                        Some((f, given)) => {
                            if let Some(op) = self.leaf(f, &given) {
                                if let Instr::Op(Rhs::Atom(Atom::Var(x))) = &op {
                                    if let Some(k) = known.get(x).cloned() {
                                        known.insert(h, k);
                                    }
                                }
                                self.out[pc] = op;
                            } else {
                                let after = rest(&self.out).filter(|code| {
                                    self.can_inline(f, given.len(), chain, code.len() + 2 + weight)
                                });
                                match after {
                                    Some(code) => {
                                        let k = Rc::new(Follow {
                                            code,
                                            base: h,
                                            chain: chain.to_vec(),
                                            next: follow.clone(),
                                        });
                                        let at = self.inline(f, &given, h, &known, chain, Some(k));
                                        self.out[pc] = Instr::Jump(at);
                                        dead = true;
                                    }
                                    None => self.out[pc] = Instr::CallFn(f, given),
                                }
                            }
                        }
                        None => {
                            if last {
                                if let Some(k) = &follow {
                                    let call = Instr::Call(Atom::Var(*i), args.clone());
                                    let at = self.resume(call, h, &known, k);
                                    self.out[pc] = Instr::Jump(at);
                                }
                                dead = true;
                            } else if returned && follow.is_none() {
                                self.out[pc] = Instr::Tail(Atom::Var(*i), args.clone());
                                dead = true;
                            }
                        }
                    }
                }
                // Whatever else ends the activation by running something
                // whose result is the activation's: with something to
                // follow, it is run and its result followed.
                Instr::Handle { tail: true, .. }
                | Instr::Label { tail: true, .. }
                | Instr::Guard { tail: true, .. }
                | Instr::Cell { tail: true, .. } => {
                    if let Some(k) = &follow {
                        let mut run = instr.clone();
                        match &mut run {
                            Instr::Handle { tail, .. }
                            | Instr::Label { tail, .. }
                            | Instr::Guard { tail, .. }
                            | Instr::Cell { tail, .. } => *tail = false,
                            _ => {}
                        }
                        let at = self.resume(run, h, &known, k);
                        self.out[pc] = Instr::Jump(at);
                    }
                    dead = true;
                }
                other => {
                    if other.last() {
                        dead = true;
                    }
                }
            }
            if matches!(instr, Instr::Ret(_)) {
                dead = true;
            }
            if pushes(&instr) {
                h += 1;
            }
        }
    }
}

/// What reads each local from each instruction on: one pass from the end,
/// every place an instruction leads to being further on.
fn read_from(code: &mut [Instr]) -> Option<Vec<HashSet<usize>>> {
    let n = code.len();
    let mut from: Vec<HashSet<usize>> = vec![HashSet::new(); n + 1];
    for pc in (0..n).rev() {
        let mut after = HashSet::new();
        match &code[pc] {
            Instr::Jump(t) => {
                if *t <= pc || *t > n {
                    return None;
                }
                after.extend(from[*t].iter().copied());
            }
            instr => {
                if !instr.last() {
                    after.extend(from[pc + 1].iter().copied());
                }
                if let Some(t) = instr.fail() {
                    if t <= pc || t > n {
                        return None;
                    }
                    after.extend(from[t].iter().copied());
                }
            }
        }
        after.extend(code[pc].place_var());
        for a in code[pc].atoms_mut() {
            if let Atom::Var(i) | Atom::Take(i) = *a {
                after.insert(i);
            }
        }
        from[pc] = after;
    }
    Some(from)
}

/// How many locals there are before each instruction, if the code agrees
/// with itself about that.
fn heights(code: &[Instr], start: usize) -> Option<Vec<usize>> {
    let n = code.len();
    let mut h: Vec<Option<usize>> = vec![None; n + 1];
    h[0] = Some(start);
    let set = |h: &mut Vec<Option<usize>>, at: usize, v: usize| -> bool {
        match h[at] {
            Some(old) => old == v,
            None => {
                h[at] = Some(v);
                true
            }
        }
    };
    for pc in 0..n {
        let Some(here) = h[pc] else { continue };
        let instr = &code[pc];
        let ok = match instr {
            Instr::Jump(t) => *t <= n && set(&mut h, *t, here),
            _ => {
                let through = instr.last() || set(&mut h, pc + 1, here + usize::from(pushes(instr)));
                through && instr.fail().is_none_or(|t| t <= n && set(&mut h, t, here))
            }
        };
        if !ok {
            return None;
        }
    }
    Some(h.into_iter().map(|x| x.unwrap_or(usize::MAX)).collect())
}

/// Do not make what nothing reads: a closure, a copy, a value built. What
/// made it gives an integer instead, so that the locals keep their numbers.
fn sweep(code: &mut [Instr], start: usize) {
    loop {
        let (Some(h), Some(from)) = (heights(code, start), read_from(code)) else { return };
        let mut changed = false;
        for pc in 0..code.len() {
            // (Rebinding what is not a closure goes wrong, and so is not
            // nothing; a program that was checked never does it.)
            let pure = matches!(
                &code[pc],
                Instr::Op(Rhs::Closure(..))
                    | Instr::Op(Rhs::Construct(..))
                    | Instr::Op(Rhs::Rebind(..))
                    | Instr::Op(Rhs::Atom(Atom::Var(_)))
            );
            if pure && h[pc] != usize::MAX && !from[pc + 1].contains(&h[pc]) {
                // (Code jumped to from here is what `from[pc + 1]` holds only
                // if this is not a jump, which it is not.)
                code[pc] = Instr::Op(Rhs::Atom(Atom::Int(0)));
                changed = true;
            }
        }
        if !changed {
            return;
        }
    }
}

/// Rewrite every function of the program that says how many locals it
/// starts with.
pub fn optimise(program: &mut Program) {
    let mut plain = program.codes.clone();
    for code in &mut plain {
        untake(code);
    }
    let bare: Vec<bool> = plain.iter().map(|code| clauses_start_bare(code)).collect();
    for f in 0..plain.len() {
        let Some(start) = program.starts[f] else { continue };
        if !bare[f] {
            continue;
        }
        let mut opt = Opt { codes: &plain, starts: &program.starts, bare: &bare, out: plain[f].clone() };
        let end = opt.out.len();
        opt.out.push(Instr::Stuck);
        opt.region(0, end, start, &HashMap::new(), &[f], None);
        let mut out = opt.out;
        // What was written must still agree with itself about its locals;
        // if it does not, the function is left as it was read.
        if heights(&out, start).is_none() {
            continue;
        }
        sweep(&mut out, start);
        mark_takes(&mut out);
        program.codes[f] = out;
    }
}
