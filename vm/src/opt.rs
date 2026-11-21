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
use std::sync::Arc as Rc;

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

/// What an argument is known to be where a function is called: anything, or
/// a closure of a function with captures known so far in turn.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Shape {
    Any,
    Clo(usize, Vec<Shape>),
}

/// How deep closures inside closures are looked at.
const NEST: usize = 3;
/// The most functions made for particular arguments.
const SPECIAL: usize = 400;

/// The functions as they were read, with no moves marked, and the ones made
/// since for arguments known to be closures.
struct World {
    codes: Vec<Vec<Instr>>,
    starts: Vec<Option<usize>>,
    bare: Vec<bool>,
    /// Whether a function installs a handler as the last thing it does.
    handles: Vec<bool>,
    /// For a function made for particular arguments: where the code of the
    /// function it was made from starts, and how many locals there are then.
    entry: Vec<Option<(usize, usize)>>,
    /// The function a function was made from; itself if it was read.
    origin: Vec<usize>,
    made: HashMap<(usize, Vec<Shape>), usize>,
}

impl World {
    /// The function `f` for arguments of these shapes: its parameters are
    /// what the closures among them captured, and it starts by making the
    /// closures again, which is then known of them all through its code.
    fn special(&mut self, f: usize, shapes: &[Shape]) -> Option<usize> {
        let key = (f, shapes.to_vec());
        if let Some(made) = self.made.get(&key) {
            return Some(*made);
        }
        if self.made.len() >= SPECIAL || !self.bare[f] || self.starts[f] != Some(shapes.len()) {
            return None;
        }
        fn leaves(s: &Shape) -> usize {
            match s {
                Shape::Any => 1,
                Shape::Clo(_, inner) => inner.iter().map(leaves).sum(),
            }
        }
        let params: usize = shapes.iter().map(leaves).sum();
        let mut code: Vec<Instr> = Vec::new();
        // A closure inside a closure is made first, as a local of its own.
        fn inner(s: &Shape, next: &mut usize, params: usize, code: &mut Vec<Instr>) -> Atom {
            match s {
                Shape::Any => {
                    *next += 1;
                    Atom::Var(*next - 1)
                }
                Shape::Clo(g, parts) => {
                    let caps: Vec<Atom> = parts.iter().map(|p| inner(p, next, params, code)).collect();
                    code.push(Instr::Op(Rhs::Closure(*g, caps)));
                    Atom::Var(params + code.len() - 1)
                }
            }
        }
        let mut next = 0;
        let mut given: Vec<Instr> = Vec::new();
        for s in shapes {
            match s {
                Shape::Any => {
                    given.push(Instr::Op(Rhs::Atom(Atom::Var(next))));
                    next += 1;
                }
                Shape::Clo(g, parts) => {
                    let caps: Vec<Atom> = parts.iter().map(|p| inner(p, &mut next, params, &mut code)).collect();
                    given.push(Instr::Op(Rhs::Closure(*g, caps)));
                }
            }
        }
        // Then the arguments in order, as the function's code numbers them.
        let base = params + code.len();
        code.extend(given);
        let body = code.len();
        if body + self.codes[f].len() >= LIMIT {
            return None;
        }
        let moved_code: Vec<Instr> = self.codes[f].iter().map(|i| moved(i, base, body)).collect();
        code.extend(moved_code);
        let made = self.codes.len();
        self.codes.push(code);
        self.starts.push(Some(params));
        self.bare.push(false);
        self.handles.push(self.handles[f]);
        self.entry.push(Some((body, base + shapes.len())));
        self.origin.push(self.origin[f]);
        self.made.insert(key, made);
        Some(made)
    }
}

struct Opt<'a> {
    world: &'a mut World,
    out: Vec<Instr>,
}

impl Opt<'_> {
    /// What a value given where a function is called is known to be.
    fn shape(&self, a: &Atom, known: &HashMap<usize, Known>, depth: usize) -> Shape {
        match a {
            Atom::Var(x) if depth < NEST => match known.get(x) {
                Some(Known::Clo(g, caps)) => {
                    Shape::Clo(*g, caps.iter().map(|c| self.shape(c, known, depth + 1)).collect())
                }
                _ => Shape::Any,
            },
            _ => Shape::Any,
        }
    }

    /// The values a function made for these shapes is given: what the
    /// closures captured, in order.
    fn flat(&self, a: &Atom, s: &Shape, known: &HashMap<usize, Known>, out: &mut Vec<Atom>) {
        match (s, a) {
            (Shape::Clo(_, parts), Atom::Var(x)) => {
                if let Some(Known::Clo(_, caps)) = known.get(x) {
                    for (c, p) in caps.iter().zip(parts) {
                        self.flat(c, p, known, out);
                    }
                }
            }
            _ => out.push(a.clone()),
        }
    }

    /// The function to call, and what to give it, when some of what `f` is
    /// given are known closures.
    fn specialise(&mut self, f: usize, given: &[Atom], known: &HashMap<usize, Known>) -> Option<(usize, Vec<Atom>)> {
        let shapes: Vec<Shape> = given.iter().map(|a| self.shape(a, known, 0)).collect();
        if shapes.iter().all(|s| *s == Shape::Any) {
            return None;
        }
        let made = self.world.special(f, &shapes)?;
        let mut flat = Vec::new();
        for (a, s) in given.iter().zip(&shapes) {
            self.flat(a, s, known, &mut flat);
        }
        Some((made, flat))
    }

    /// A function that is one computation of its arguments, given back, or
    /// that gives back one of them.
    fn leaf(&self, f: usize, given: &[Atom]) -> Option<Instr> {
        let code = &self.world.codes[f];
        if self.world.starts[f] != Some(given.len()) {
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
        let code = &self.world.codes[f];
        let ends = code.iter().filter(|i| i.last()).count();
        code.len() <= CALLEE
            && self.world.bare[f]
            && self.world.starts[f] == Some(given)
            && !chain.contains(&f)
            && chain.len() < DEPTH
            && self.out.len() + code.len() + given + ends * follow < LIMIT
            // A handler is written in place only where nothing follows it, so
            // a function that installs one is left a function where
            // something does.
            && !(follow > 0 && self.world.handles[f])
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
        first: Option<Instr>,
    ) -> usize {
        let at = self.out.len();
        self.out.extend(first);
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
        let code = &self.world.codes[f];
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
                                let at = self.inline(f, &given, h, &known, chain, follow.clone(), None);
                                self.out[pc] = Instr::Jump(at);
                                dead = true;
                            } else {
                                // The function made for the closures it is
                                // given, if it is given any.
                                let (f, given) = self.specialise(f, &given, &known).unwrap_or((f, given));
                                if let Some(k) = &follow {
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
                                        let at = self.inline(f, &given, h, &known, chain, Some(k), None);
                                        self.out[pc] = Instr::Jump(at);
                                        dead = true;
                                    }
                                    None => {
                                        let (f, given) = self.specialise(f, &given, &known).unwrap_or((f, given));
                                        self.out[pc] = Instr::CallFn(f, given);
                                    }
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
                // A handler installed as the last thing, around a callable
                // that is known and with nothing to follow: the handler is
                // installed and the callable's code written here. Where it
                // gives a value the handler is removed and the handler's
                // clause for a value is called with it, as it would be.
                Instr::Handle { ret, ops, caps, thunk: Atom::Var(i), tail: true }
                    if follow.is_none()
                        && matches!(known.get(i), Some(Known::Clo(t, tcaps))
                            if self.can_inline(*t, tcaps.len(), chain, 6)) =>
                {
                    let Some(Known::Clo(t, tcaps)) = known.get(i).cloned() else { unreachable!() };
                    let leave = Rc::new(Follow {
                        code: vec![
                            Instr::Leave,
                            Instr::Op(Rhs::Closure(*ret, caps.clone())),
                            Instr::Tail(Atom::Var(h + 1), vec![Atom::Var(h)]),
                        ],
                        base: h,
                        chain: chain.to_vec(),
                        next: None,
                    });
                    let enter = Instr::Enter { ret: *ret, ops: ops.clone(), caps: caps.clone() };
                    let at = self.inline(t, &tcaps, h, &known, chain, Some(leave), Some(enter));
                    self.out[pc] = Instr::Jump(at);
                    dead = true;
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

/// Do not make what nothing reads: a closure, a copy, a value built. What
/// made it gives an integer instead, so that the locals keep their numbers.
fn sweep(code: &mut [Instr], start: usize) {
    // (Rebinding what is not a closure goes wrong, and so is not nothing; a
    // program that was checked never does it.)
    let pure = |i: &Instr| {
        matches!(
            i,
            Instr::Op(Rhs::Closure(..))
                | Instr::Op(Rhs::Construct(..))
                | Instr::Op(Rhs::Rebind(..))
                | Instr::Op(Rhs::Atom(Atom::Var(_)))
        )
    };
    let Some(h) = heights(code, start) else { return };
    // (What such instructions read only for each other is not read, so all
    // of them are found at once.)
    let from = read_from_but(code, Some(start), pure);
    for pc in 0..code.len() {
        if pure(&code[pc]) && h[pc] != usize::MAX && !from[pc + 1].contains(h[pc]) {
            code[pc] = Instr::Op(Rhs::Atom(Atom::Int(0)));
        }
    }
}

/// The instruction run after this one where there is one and only one way on
/// and nothing is done but to go there or to make a value.
fn next_plain(code: &[Instr], pc: usize) -> Option<usize> {
    match &code[pc] {
        Instr::Jump(t) => Some(*t),
        Instr::Op(_) => Some(pc + 1),
        _ => None,
    }
}

/// A function that calls itself last, with what it was given, goes back to
/// its start instead, letting go of the locals it made since. If it starts
/// by installing a handler, and removes it before it calls itself, the
/// handler is left where it is and the function goes back to just after it
/// was installed: what would be installed again is the same.
fn again(code: &mut [Instr], f: usize, start: usize) {
    let own = |given: &[Atom]| {
        given.len() == start && given.iter().enumerate().all(|(k, a)| matches!(a, Atom::Var(i) if *i == k))
    };
    let Some(h) = heights(code, start) else { return };
    // The one handler installed, if it is installed on the way in, before
    // anything but values are made.
    let enters: Vec<usize> = (0..code.len()).filter(|pc| matches!(code[*pc], Instr::Enter { .. })).collect();
    let mut at = 0;
    while at < code.len() && !matches!(code[at], Instr::Enter { .. }) {
        match next_plain(code, at) {
            Some(next) if next > at => at = next,
            _ => break,
        }
    }
    let entered = (enters.len() == 1 && enters[0] == at).then_some(at);
    for pc in 0..code.len() {
        if h[pc] == usize::MAX {
            continue;
        }
        match &code[pc] {
            Instr::TailFn(g, given) if *g == f && own(given) => {
                code[pc] = Instr::Again(0, start);
            }
            Instr::Leave => {
                // From the handler's removal on to the call, nothing but
                // values made.
                let Some(enter) = entered else { continue };
                let mut q = pc + 1;
                let mut steps = 0;
                while steps < 64 && q < code.len() {
                    match &code[q] {
                        Instr::TailFn(g, given) if *g == f && own(given) => {
                            code[q] = Instr::Again(enter + 1, h[enter + 1]);
                            code[pc] = Instr::Jump(pc + 1);
                            break;
                        }
                        _ => match next_plain(code, q) {
                            Some(next) => q = next,
                            None => break,
                        },
                    }
                    steps += 1;
                }
            }
            _ => {}
        }
    }
}

/// Rewrite every function of the program that says how many locals it
/// starts with, and the functions made for particular arguments on the way.
pub fn optimise(program: &mut Program) {
    let mut plain = program.codes.clone();
    for code in &mut plain {
        untake(code);
    }
    let bare: Vec<bool> = plain.iter().map(|code| clauses_start_bare(code)).collect();
    let handles: Vec<bool> =
        plain.iter().map(|code| code.iter().any(|i| matches!(i, Instr::Handle { .. }))).collect();
    let mut world = World {
        entry: vec![None; plain.len()],
        origin: (0..plain.len()).collect(),
        codes: plain,
        starts: program.starts.clone(),
        bare,
        handles,
        made: HashMap::new(),
    };
    let mut f = 0;
    while f < world.codes.len() {
        let done = rewrite(&mut world, f);
        if f < program.codes.len() {
            if let Some(code) = done {
                program.codes[f] = code;
            }
        } else {
            // A function made here has no code but what is written for it.
            // (Moves are marked once: marking reads a move as no reading.)
            let code = done.unwrap_or_else(|| {
                let mut code = world.codes[f].clone();
                mark_takes(&mut code, None);
                code
            });
            program.codes.push(code);
            program.starts.push(world.starts[f]);
        }
        f += 1;
    }
}

/// The function's code rewritten, or nothing if it is left as it was read.
fn rewrite(world: &mut World, f: usize) -> Option<Vec<Instr>> {
    let start = world.starts[f]?;
    let mut out = world.codes[f].clone();
    let end = out.len();
    out.push(Instr::Stuck);
    let mut opt = Opt { world, out };
    match opt.world.entry[f] {
        None => {
            if !opt.world.bare[f] {
                return None;
            }
            opt.region(0, end, start, &HashMap::new(), &[f], None);
        }
        Some((body, height)) => {
            // Made for particular arguments: it starts by making them, and
            // what they are is known in the code that follows.
            let mut known = HashMap::new();
            for pc in 0..body {
                if let Instr::Op(Rhs::Closure(g, caps)) = &opt.out[pc] {
                    known.insert(start + pc, Known::Clo(*g, caps.clone()));
                }
            }
            let origin = opt.world.origin[f];
            opt.region(body, end, height, &known, &[f, origin], None);
        }
    }
    let mut out = opt.out;
    again(&mut out, f, start);
    // What was written must still agree with itself about its locals; if
    // it does not, the function is left as it was read.
    heights(&out, start)?;
    sweep(&mut out, start);
    mark_takes(&mut out, Some(start));
    Some(out)
}
