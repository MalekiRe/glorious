//! The Glorious virtual machine.
//!
//! This implements the bytecode semantics defined in
//! `Glorious/Bytecode/Semantics.lean`. Each rule here mirrors a rule there, and
//! the file format is the one written by `Glorious/Bytecode/Encode.lean`. A
//! state the Lean semantics gives no meaning to ends the run with
//! "the program went wrong".
//!
//! The stack is a `Vec` with its top at the end, where the Lean definitions use
//! a list with its top at the front.

use std::collections::{HashMap, VecDeque};
use std::io::{self, BufWriter, Write};
use std::process::ExitCode;
use std::rc::Rc;

// ---------------------------------------------------------------- values

/// The layout is part of the ABI (`docs/abi.md`): a tag byte at 0, and what the
/// value holds from byte 8 or, for an integer, from byte 16. Compiled code
/// reads and writes integers in place and leaves the rest to the runtime.
#[derive(Clone)]
#[repr(u8)]
pub enum Value {
    Int(i128) = 0,
    Data(Rc<Data>) = 1,
    Clo(Rc<Clo>) = 2,
    Cont(usize) = 3,
    Label(u64) = 4,
    /// A cell, and the steps to take to the part of what it holds that the
    /// reference is to: none for the whole.
    Ref(usize, Path) = 5,
}

/// A step to a field: the constructor the value has to have been built by,
/// plus one, or zero for any; and the field's number.
pub type PathStep = (u64, usize);
pub type Path = Option<Rc<[PathStep]>>;

fn steps(path: &Path) -> &[PathStep] {
    path.as_deref().unwrap_or(&[])
}

/// The part of a value that steps lead to.
fn part<'a>(mut v: &'a Value, path: &[PathStep]) -> Step<&'a Value> {
    for &(built, i) in path {
        match v {
            Value::Data(d) if built == 0 || d.tag == built - 1 => {
                v = d.fields.get(i).ok_or(Stop::Wrong)?
            }
            _ => return wrong(),
        }
    }
    Ok(v)
}

/// The same part, to change: a value that is shared is copied on the way.
fn part_mut<'a>(mut v: &'a mut Value, path: &[PathStep]) -> Step<&'a mut Value> {
    for &(built, i) in path {
        match v {
            Value::Data(d) if built == 0 || d.tag == built - 1 => {
                v = Rc::make_mut(d).fields.get_mut(i).ok_or(Stop::Wrong)?
            }
            _ => return wrong(),
        }
    }
    Ok(v)
}

#[derive(Clone)]
pub struct Data {
    tag: u64,
    fields: Vec<Value>,
}

pub struct Clo {
    func: usize,
    caps: Vec<Value>,
}

fn data(tag: u64, fields: Vec<Value>) -> Value {
    if tag == 0 && fields.is_empty() {
        return unit();
    }
    Value::Data(Rc::new(Data { tag, fields }))
}

/// The value with no parts. There is one, made once.
fn unit() -> Value {
    thread_local! {
        static UNIT: Value = Value::Data(Rc::new(Data { tag: 0, fields: Vec::new() }));
    }
    UNIT.with(Value::clone)
}

// ---------------------------------------------------------------- code

#[derive(Clone, Debug)]
enum Atom {
    Var(usize),
    /// The local, which nothing reads again: its value is moved, not copied.
    /// No file has these; they are found when a program is loaded.
    Take(usize),
    Int(i128),
}

#[derive(Clone, Debug)]
struct Place {
    var: usize,
    path: Vec<usize>,
}

#[derive(Debug, Clone, Copy)]
enum Prim {
    Add,
    Sub,
    Mul,
    Lt,
    Eq,
    Div,
    Rem,
    Fit,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FLt,
    FEq,
    FOfInt,
    FToInt,
    FNarrow,
    FWiden,
    FOfDecimal,
    FDigits,
    FExp10,
    FSqrt,
    FRound,
    WAdd,
    WSub,
    WMul,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    UAdd,
    USub,
    UMul,
    UDiv,
    URem,
    ULt,
    UShl,
    UShr,
    Below,
    ArrGet,
    ArrSet,
    ArrLen,
    ArrPush,
    ArrPop,
}

#[derive(Debug, Clone, Copy)]
enum MemOp {
    Load,
    Store,
    Swap,
    Tag,
    Focus,
}

#[derive(Clone, Debug)]
enum Rhs {
    Atom(Atom),
    Prim(Prim, Vec<Atom>),
    Construct(u64, Vec<Atom>),
    Place(Place),
    Closure(usize, Vec<Atom>),
    Rebind(Atom, usize),
}

#[derive(Clone, Debug)]
enum Instr {
    Op(Rhs),
    Call(Atom, Vec<Atom>),
    Tail(Atom, Vec<Atom>),
    Ret(Atom),
    Handle { ret: usize, ops: Vec<(u64, usize)>, caps: Vec<Atom>, thunk: Atom, tail: bool },
    Raise(u64, Vec<Atom>),
    Perform(u64, Vec<Atom>),
    Label { thunk: Atom, tail: bool },
    Guard { cleanup: Atom, thunk: Atom, tail: bool },
    Cancel(Atom),
    Host(u64, Vec<Atom>),
    TestCtor(Place, u64, usize, usize),
    TestInt(Place, i128, usize),
    Mem(MemOp, Vec<Atom>),
    Cell { init: Atom, thunk: Atom, tail: bool },
    Lend { r: Atom, thunk: Atom, pre: Vec<Atom>, post: Vec<Atom> },
    // No file has the three below: they are written when a program is
    // loaded (`opt.rs`).
    /// A call of a function that is known: its locals are these values.
    CallFn(usize, Vec<Atom>),
    /// The same as the last thing the activation does.
    TailFn(usize, Vec<Atom>),
    /// Go on from another instruction of the function.
    Jump(usize),
    /// Where a test that fails in a function's last clause goes: the program
    /// has gone wrong.
    Stuck,
    /// Install a handler around what this activation does next.
    Enter { ret: usize, ops: Vec<(u64, usize)>, caps: Vec<Atom> },
    /// Remove the handler this activation installed.
    Leave,
    /// Go back to an instruction with only so many locals: the rest are
    /// let go of. What a function that calls itself last, with what it was
    /// given, comes to.
    Again(usize, usize),
}

// ---------------------------------------------------------------- decoding

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

type Decoded<T> = Result<T, String>;

impl Reader<'_> {
    fn byte(&mut self) -> Decoded<u8> {
        let b = *self.bytes.get(self.pos).ok_or("unexpected end of file")?;
        self.pos += 1;
        Ok(b)
    }

    /// Little-endian base 128; every byte but the last has its top bit set.
    fn nat(&mut self) -> Decoded<u64> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let chunk = u64::from(b & 0x7f);
            if shift >= 64 || (chunk << shift) >> shift != chunk {
                return Err("number does not fit in 64 bits".into());
            }
            result |= chunk << shift;
            if b < 128 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    fn index(&mut self) -> Decoded<usize> {
        usize::try_from(self.nat()?).map_err(|_| "index too large".into())
    }

    /// A number of up to 128 bits, in the same form.
    fn wide(&mut self) -> Decoded<u128> {
        let mut result: u128 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            let chunk = u128::from(b & 0x7f);
            if shift >= 128 || (chunk << shift) >> shift != chunk {
                return Err("number does not fit in 128 bits".into());
            }
            result |= chunk << shift;
            if b < 128 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    /// Zigzag: `2m` is `m`, `2m + 1` is `-(m + 1)`.
    fn int(&mut self) -> Decoded<i128> {
        let z = self.wide()?;
        let half = (z >> 1) as i128;
        Ok(if z & 1 == 0 { half } else { -half - 1 })
    }

    fn list<T>(&mut self, mut item: impl FnMut(&mut Self) -> Decoded<T>) -> Decoded<Vec<T>> {
        let len = self.index()?;
        let mut out = Vec::with_capacity(len.min(1 << 16));
        for _ in 0..len {
            out.push(item(self)?);
        }
        Ok(out)
    }

    fn atom(&mut self) -> Decoded<Atom> {
        match self.byte()? {
            0 => Ok(Atom::Var(self.index()?)),
            1 => Ok(Atom::Int(self.int()?)),
            t => Err(format!("unknown operand tag {t}")),
        }
    }

    fn atoms(&mut self) -> Decoded<Vec<Atom>> {
        self.list(Self::atom)
    }

    fn place(&mut self) -> Decoded<Place> {
        let var = self.index()?;
        let path = self.list(Self::index)?;
        Ok(Place { var, path })
    }

    fn prim(&mut self) -> Decoded<Prim> {
        match self.byte()? {
            0 => Ok(Prim::Add),
            1 => Ok(Prim::Sub),
            2 => Ok(Prim::Mul),
            3 => Ok(Prim::Lt),
            4 => Ok(Prim::Eq),
            5 => Ok(Prim::Div),
            6 => Ok(Prim::Rem),
            7 => Ok(Prim::Fit),
            8 => Ok(Prim::FAdd),
            9 => Ok(Prim::FSub),
            10 => Ok(Prim::FMul),
            11 => Ok(Prim::FDiv),
            12 => Ok(Prim::FLt),
            13 => Ok(Prim::FEq),
            14 => Ok(Prim::FOfInt),
            15 => Ok(Prim::FToInt),
            16 => Ok(Prim::FNarrow),
            17 => Ok(Prim::FWiden),
            18 => Ok(Prim::FOfDecimal),
            19 => Ok(Prim::FDigits),
            20 => Ok(Prim::FExp10),
            21 => Ok(Prim::FSqrt),
            22 => Ok(Prim::FRound),
            23 => Ok(Prim::WAdd),
            24 => Ok(Prim::WSub),
            25 => Ok(Prim::WMul),
            26 => Ok(Prim::And),
            27 => Ok(Prim::Or),
            28 => Ok(Prim::Xor),
            29 => Ok(Prim::Shl),
            30 => Ok(Prim::Shr),
            31 => Ok(Prim::UAdd),
            32 => Ok(Prim::USub),
            33 => Ok(Prim::UMul),
            34 => Ok(Prim::UDiv),
            35 => Ok(Prim::URem),
            36 => Ok(Prim::ULt),
            37 => Ok(Prim::UShl),
            38 => Ok(Prim::UShr),
            39 => Ok(Prim::Below),
            40 => Ok(Prim::ArrGet),
            41 => Ok(Prim::ArrSet),
            42 => Ok(Prim::ArrLen),
            43 => Ok(Prim::ArrPush),
            44 => Ok(Prim::ArrPop),
            t => Err(format!("unknown intrinsic {t}")),
        }
    }

    fn rhs(&mut self) -> Decoded<Rhs> {
        match self.byte()? {
            0 => Ok(Rhs::Atom(self.atom()?)),
            1 => {
                let p = self.prim()?;
                Ok(Rhs::Prim(p, self.atoms()?))
            }
            2 => {
                let tag = self.nat()?;
                Ok(Rhs::Construct(tag, self.atoms()?))
            }
            3 => Ok(Rhs::Place(self.place()?)),
            4 => {
                let func = self.index()?;
                Ok(Rhs::Closure(func, self.atoms()?))
            }
            5 => {
                let a = self.atom()?;
                Ok(Rhs::Rebind(a, self.index()?))
            }
            t => Err(format!("unknown computation tag {t}")),
        }
    }

    fn handle(&mut self, tail: bool) -> Decoded<Instr> {
        let ret = self.index()?;
        let ops = self.list(|r| Ok((r.nat()?, r.index()?)))?;
        let caps = self.atoms()?;
        let thunk = self.atom()?;
        Ok(Instr::Handle { ret, ops, caps, thunk, tail })
    }

    fn guard(&mut self, tail: bool) -> Decoded<Instr> {
        let cleanup = self.atom()?;
        let thunk = self.atom()?;
        Ok(Instr::Guard { cleanup, thunk, tail })
    }

    fn cell(&mut self, tail: bool) -> Decoded<Instr> {
        let init = self.atom()?;
        let thunk = self.atom()?;
        Ok(Instr::Cell { init, thunk, tail })
    }

    fn instr(&mut self) -> Decoded<Instr> {
        match self.byte()? {
            0 => Ok(Instr::Op(self.rhs()?)),
            1 => {
                let f = self.atom()?;
                Ok(Instr::Call(f, self.atoms()?))
            }
            2 => {
                let f = self.atom()?;
                Ok(Instr::Tail(f, self.atoms()?))
            }
            3 => Ok(Instr::Ret(self.atom()?)),
            4 => self.handle(false),
            5 => self.handle(true),
            6 => {
                let op = self.nat()?;
                Ok(Instr::Raise(op, self.atoms()?))
            }
            7 => {
                let op = self.nat()?;
                Ok(Instr::Perform(op, self.atoms()?))
            }
            8 => Ok(Instr::Label { thunk: self.atom()?, tail: false }),
            9 => Ok(Instr::Label { thunk: self.atom()?, tail: true }),
            10 => self.guard(false),
            11 => self.guard(true),
            12 => Ok(Instr::Cancel(self.atom()?)),
            13 => {
                let id = self.nat()?;
                Ok(Instr::Host(id, self.atoms()?))
            }
            14 => {
                let pl = self.place()?;
                let tag = self.nat()?;
                let arity = self.index()?;
                Ok(Instr::TestCtor(pl, tag, arity, self.index()?))
            }
            15 => {
                let pl = self.place()?;
                let n = self.int()?;
                Ok(Instr::TestInt(pl, n, self.index()?))
            }
            16 => {
                let op = match self.byte()? {
                    0 => MemOp::Load,
                    1 => MemOp::Store,
                    2 => MemOp::Swap,
                    3 => MemOp::Tag,
                    4 => MemOp::Focus,
                    t => return Err(format!("unknown memory operation {t}")),
                };
                Ok(Instr::Mem(op, self.atoms()?))
            }
            17 => self.cell(false),
            18 => self.cell(true),
            19 => {
                // Whether the borrow is for writing too: the machine does not use it.
                let uniq = self.byte()?;
                if uniq > 1 {
                    return Err(format!("unknown kind of borrow {uniq}"));
                }
                let r = self.atom()?;
                let thunk = self.atom()?;
                let pre = self.atoms()?;
                let post = self.atoms()?;
                Ok(Instr::Lend { r, thunk, pre, post })
            }
            t => Err(format!("unknown instruction {t}")),
        }
    }

    fn code(&mut self) -> Decoded<Vec<Instr>> {
        self.list(Self::instr)
    }

    fn string(&mut self) -> Decoded<String> {
        let bytes = self.list(Self::byte)?;
        String::from_utf8(bytes).map_err(|_| "a name is not valid UTF-8".into())
    }
}

// ------------------------------------------------------------ last readings

impl Instr {
    /// The operands of an instruction that are values of locals.
    fn atoms_mut(&mut self) -> Vec<&mut Atom> {
        match self {
            Instr::Op(Rhs::Atom(a)) | Instr::Op(Rhs::Rebind(a, _)) => vec![a],
            Instr::Op(Rhs::Prim(_, xs))
            | Instr::Op(Rhs::Construct(_, xs))
            | Instr::Op(Rhs::Closure(_, xs)) => xs.iter_mut().collect(),
            Instr::Op(Rhs::Place(_)) => vec![],
            Instr::Call(f, xs) | Instr::Tail(f, xs) => {
                std::iter::once(f).chain(xs.iter_mut()).collect()
            }
            Instr::Ret(a) | Instr::Cancel(a) => vec![a],
            Instr::Handle { caps, thunk, .. } => {
                caps.iter_mut().chain(std::iter::once(thunk)).collect()
            }
            Instr::Raise(_, xs)
            | Instr::Perform(_, xs)
            | Instr::Host(_, xs)
            | Instr::Mem(_, xs)
            | Instr::CallFn(_, xs)
            | Instr::TailFn(_, xs) => xs.iter_mut().collect(),
            Instr::Jump(_) | Instr::Stuck | Instr::Leave | Instr::Again(..) => vec![],
            Instr::Enter { caps, .. } => caps.iter_mut().collect(),
            Instr::Label { thunk, .. } => vec![thunk],
            Instr::Guard { cleanup, thunk, .. } => vec![cleanup, thunk],
            Instr::TestCtor(..) | Instr::TestInt(..) => vec![],
            Instr::Cell { init, thunk, .. } => vec![init, thunk],
            Instr::Lend { r, thunk, pre, post } => {
                [r, thunk].into_iter().chain(pre.iter_mut()).chain(post.iter_mut()).collect()
            }
        }
    }

    /// The local an instruction reads a field of, if it reads one.
    fn place_var(&self) -> Option<usize> {
        match self {
            Instr::Op(Rhs::Place(pl)) | Instr::TestCtor(pl, ..) | Instr::TestInt(pl, ..) => {
                Some(pl.var)
            }
            _ => None,
        }
    }

    /// Where a test goes when it fails.
    fn fail(&self) -> Option<usize> {
        match self {
            Instr::TestCtor(_, _, _, fail) | Instr::TestInt(_, _, fail) => Some(*fail),
            _ => None,
        }
    }

    /// Does the activation end here, with nothing of it run afterwards?
    fn last(&self) -> bool {
        match self {
            Instr::Tail(..) | Instr::TailFn(..) | Instr::Ret(_) | Instr::Raise(..) | Instr::Stuck => true,
            Instr::Handle { tail, .. }
            | Instr::Label { tail, .. }
            | Instr::Guard { tail, .. }
            | Instr::Cell { tail, .. } => *tail,
            _ => false,
        }
    }
}

/// Where an instruction may be followed from: the next, where its test
/// fails, where it jumps.
fn follows(code: &[Instr], pc: usize) -> Vec<usize> {
    match &code[pc] {
        Instr::Jump(t) | Instr::Again(t, _) => vec![*t],
        instr => {
            let mut out = Vec::new();
            if !instr.last() {
                out.push(pc + 1);
            }
            out.extend(instr.fail());
            out
        }
    }
}

/// Does the instruction give a value, which is then the next local?
fn pushes(instr: &Instr) -> bool {
    !instr.last()
        && instr.fail().is_none()
        && !matches!(instr, Instr::Jump(_) | Instr::Enter { .. } | Instr::Leave | Instr::Again(..))
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
            Instr::Again(t, keep) => *t <= n && *keep <= here && set(&mut h, *t, *keep),
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

/// A set of locals, one bit each.
#[derive(Clone, PartialEq)]
struct Locals(Vec<u64>);

impl Locals {
    fn new(words: usize) -> Self {
        Locals(vec![0; words])
    }
    fn insert(&mut self, i: usize) {
        if let Some(w) = self.0.get_mut(i / 64) {
            *w |= 1 << (i % 64);
        }
    }
    fn contains(&self, i: usize) -> bool {
        self.0.get(i / 64).is_some_and(|w| w & (1 << (i % 64)) != 0)
    }
}

/// The locals read from each instruction on, a move counting as a reading.
/// Code may go back, so this is gone over until nothing changes. Where the
/// number of locals the code starts with is known, so is the local each
/// instruction makes, and a local is not read before it is made.
fn read_from(code: &mut [Instr], start: Option<usize>) -> Vec<Locals> {
    read_from_but(code, start, |_| false)
}

/// The same, where an instruction `idle` says gives what nothing needs
/// reads nothing if nothing reads what it gives: what such instructions read
/// only for each other is not read. (So what a sweep takes away is found in
/// one go, not one layer of them at a time.)
fn read_from_but(code: &mut [Instr], start: Option<usize>, idle: impl Fn(&Instr) -> bool) -> Vec<Locals> {
    let n = code.len();
    let made: Vec<Option<usize>> = match start.and_then(|s| heights(code, s)) {
        Some(h) => (0..n).map(|pc| (pushes(&code[pc]) && h[pc] != usize::MAX).then_some(h[pc])).collect(),
        None => vec![None; n],
    };
    let reads: Vec<Vec<usize>> = (0..n)
        .map(|pc| {
            let mut r: Vec<usize> = code[pc].place_var().into_iter().collect();
            for a in code[pc].atoms_mut() {
                if let Atom::Var(i) | Atom::Take(i) = *a {
                    r.push(i);
                }
            }
            r
        })
        .collect();
    let most = reads.iter().flatten().copied().max().unwrap_or(0);
    let words = most / 64 + 1;
    let nexts: Vec<Vec<usize>> = (0..n).map(|pc| follows(code, pc).into_iter().filter(|&x| x <= n).collect()).collect();
    let mut from: Vec<Locals> = vec![Locals::new(words); n + 1];
    // (One set worked in, swapped in where it differs: no allocation per
    // instruction.)
    let mut here = Locals::new(words);
    loop {
        let mut changed = false;
        for pc in (0..n).rev() {
            here.0.iter_mut().for_each(|w| *w = 0);
            for &next in &nexts[pc] {
                for (w, o) in here.0.iter_mut().zip(from[next].0.iter()) {
                    *w |= *o;
                }
            }
            // (What this instruction makes is not read before it.)
            let needed = made[pc].is_none_or(|m| here.contains(m));
            if let Some(m) = made[pc] {
                if let Some(w) = here.0.get_mut(m / 64) {
                    *w &= !(1 << (m % 64));
                }
            }
            if needed || !idle(&code[pc]) {
                for &i in &reads[pc] {
                    here.insert(i);
                }
            }
            if here != from[pc] {
                std::mem::swap(&mut here, &mut from[pc]);
                changed = true;
            }
        }
        if !changed {
            return from;
        }
    }
}

/// Make each reading of a local that nothing reads afterwards a move.
fn mark_takes(code: &mut [Instr], start: Option<usize>) {
    let from = read_from(code, start);
    let n = code.len();
    let words = from.first().map_or(1, |l| l.0.len());
    for pc in 0..n {
        let mut after = Locals::new(words);
        for next in follows(code, pc) {
            if next <= n {
                for (w, o) in after.0.iter_mut().zip(from[next].0.iter()) {
                    *w |= *o;
                }
            }
        }
        let place = code[pc].place_var();
        let mut times: Vec<(usize, usize)> = Vec::new();
        for a in code[pc].atoms_mut() {
            if let Atom::Var(i) = a {
                match times.iter_mut().find(|(j, _)| j == i) {
                    Some((_, c)) => *c += 1,
                    None => times.push((*i, 1)),
                }
            }
        }
        for a in code[pc].atoms_mut() {
            if let Atom::Var(i) = *a {
                let once = times.iter().any(|&(j, c)| j == i && c == 1);
                if !after.contains(i) && once && place != Some(i) {
                    *a = Atom::Take(i);
                }
            }
        }
    }
}

struct Program {
    names: Vec<String>,
    /// The functions, followed by the main code.
    codes: Vec<Vec<Instr>>,
    /// How many locals each function starts with, where the file says.
    starts: Vec<Option<usize>>,
    /// Which of `codes` is the main code: the last as the file has them.
    /// Functions made when the program is loaded come after it.
    main: usize,
    /// For each function whose closures say how they are destroyed, the
    /// function that destroys what one captured.
    drops: HashMap<usize, usize>,
}

fn decode(bytes: &[u8], rewrite: bool) -> Decoded<Program> {
    if bytes.len() < 5 || &bytes[..4] != b"GLBC" {
        return Err("not a Glorious bytecode file".into());
    }
    if bytes[4] != 6 {
        return Err(format!("unsupported bytecode version {}", bytes[4]));
    }
    let mut r = Reader { bytes, pos: 5 };
    let names = r.list(Reader::string)?;
    let mut codes = r.list(Reader::code)?;
    codes.push(r.code()?);
    let mut drops = HashMap::new();
    for _ in 0..r.nat()? {
        let f = r.nat()? as usize;
        let d = r.nat()? as usize;
        if f + 1 >= codes.len() || d + 1 >= codes.len() {
            return Err("a destructor names no function".into());
        }
        // As `List.lookup`: the first entry for a function is the one used.
        drops.entry(f).or_insert(d);
    }
    for code in &mut codes {
        mark_takes(code, None);
    }
    // What follows the program, if anything does: how many locals each
    // function starts with, and one more, or zero where that is not known.
    let mut starts = vec![None; codes.len()];
    if r.pos != bytes.len() {
        for (f, n) in r.list(Reader::nat)?.into_iter().enumerate() {
            if f + 1 < codes.len() && n > 0 {
                starts[f] = Some(n as usize - 1);
            }
        }
        // The main code starts with none.
        *starts.last_mut().unwrap() = Some(0);
    }
    if r.pos != bytes.len() {
        return Err("trailing bytes after the program".into());
    }
    let main = codes.len() - 1;
    let mut program = Program { names, codes, starts, main, drops };
    if rewrite {
        opt::optimise(&mut program);
    }
    Ok(program)
}

// ---------------------------------------------------------------- machine

struct Handler {
    ret: usize,
    ops: Vec<(u64, usize)>,
    caps: Vec<Value>,
}

/// Where an exit is going: a label scope or a handler, by its identity.
#[derive(Clone, Copy, PartialEq)]
enum Target {
    Label(u64),
    Handler(u64),
}

/// What an exit does once it has arrived and removed its target.
enum After {
    Yield(Value),
    Invoke { func: usize, caps: Vec<Value>, args: Vec<Value> },
}

enum Frame {
    /// Where to continue after a call returns, and the locals to restore.
    Ret { code: usize, pc: usize, locals: Vec<Value> },
    /// The delimiter of an installed handler, with its identity.
    Handler { id: u64, handler: Rc<Handler> },
    /// The scope of a label.
    Label(u64),
    /// A cleanup that runs when the computation above it is left.
    Guard { func: usize, caps: Vec<Value> },
    /// The scope of a memory cell: the cell is released when this frame is removed.
    Cell(usize),
    /// A pending result: what is delivered here is discarded and this is delivered.
    Yield(Value),
    /// An exit in progress: a cleanup was running above this frame. What it
    /// delivers is discarded and the exit continues towards its target.
    Exit { target: Target, after: After },
    /// Below this, a foreign function is waiting for what it called to give
    /// a value. Nothing passes it but that value: no effect, no exit.
    Boundary,
}

impl Frame {
    fn is_target(&self, target: Target) -> bool {
        match (self, target) {
            (Frame::Label(id), Target::Label(wanted)) => *id == wanted,
            (Frame::Handler { id, .. }, Target::Handler(wanted)) => *id == wanted,
            _ => false,
        }
    }
}

/// Why the machine stopped.
enum Stop {
    Halt(Value),
    Wrong,
    /// What a foreign function called has given its value.
    Back(Value),
}

type Step<T> = Result<T, Stop>;

fn wrong<T>() -> Step<T> {
    Err(Stop::Wrong)
}

// The foreign boundary. Nothing here is checked: an address is whatever the
// program says it is, and a foreign function is whatever the name finds.

extern "C" {
    fn dlsym(handle: *mut u8, symbol: *const u8) -> *mut u8;
    fn dlopen(name: *const u8, flags: i32) -> *mut u8;
    fn fflush(stream: *mut u8) -> i32;
}

/// The low `width` bits of what C gave: with a sign if `width` is positive,
/// without one if it is negative.
fn sized(raw: u128, width: i128) -> i128 {
    let bits = width.unsigned_abs() as u32;
    if bits == 0 || bits >= 128 {
        return raw as i128;
    }
    let low = raw & ((1u128 << bits) - 1);
    if width > 0 && low >> (bits - 1) == 1 {
        (low as i128) - (1i128 << bits)
    } else {
        low as i128
    }
}

fn read_at(at: usize, bytes: usize) -> u128 {
    let mut out = [0u8; 16];
    let n = bytes.min(16);
    // SAFETY: none. The program said this address holds so many bytes.
    unsafe { std::ptr::copy_nonoverlapping(at as *const u8, out.as_mut_ptr(), n) };
    u128::from_le_bytes(out)
}

fn write_at(at: usize, bytes: usize, v: u128) {
    let n = bytes.min(16);
    // SAFETY: none. The program said this address has room for so many bytes.
    unsafe { std::ptr::copy_nonoverlapping(v.to_le_bytes().as_ptr(), at as *mut u8, n) };
}

/// Call the C function whose name the first values spell, up to a zero; then
/// how many bits it gives, and what it is given: up to six whole numbers.
fn foreign_call(vs: &[Value]) -> Option<Value> {
    let ints: Vec<i128> = vs
        .iter()
        .map(|v| match v {
            Value::Int(n) => Some(*n),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let end = ints.iter().position(|n| *n == 0)?;
    let mut name: Vec<u8> = ints[..end].iter().map(|n| *n as u8).collect();
    name.push(0);
    let width = *ints.get(end + 1)?;
    // Where C takes each value: digit `i` in base three is 0 for a whole
    // number or an address, 1 for a double, 2 for a float.
    let mut classes = *ints.get(end + 2)?;
    let mut whole = [0usize; 6];
    let mut real = [0f64; 8];
    let (mut wholes, mut reals) = (0, 0);
    for n in &ints[end + 3..] {
        let class = classes % 3;
        classes /= 3;
        if class == 0 {
            if wholes == 6 {
                eprintln!("a foreign function is given at most six whole numbers and addresses");
                return None;
            }
            whole[wholes] = *n as usize;
            wholes += 1;
        } else {
            if reals == 8 {
                eprintln!("a foreign function is given at most eight floats");
                return None;
            }
            // A float is the low half of the place a double would be in.
            let bits = if class == 1 { *n as u64 } else { u64::from(*n as u32) };
            real[reals] = f64::from_bits(bits);
            reals += 1;
        }
    }
    // SAFETY: none beyond the name being found. The program said what the
    // function takes. Every place C could look for a value is given one:
    // a function reads only those it takes.
    let raw: u128 = unsafe {
        let mut f = dlsym(std::ptr::null_mut(), name.as_ptr());
        if f.is_null() {
            // What is not in the process yet may be in C's library of
            // mathematics, which a program names without saying so.
            let math = dlopen(b"libm.so.6\0".as_ptr(), 2);
            if !math.is_null() {
                f = dlsym(math, name.as_ptr());
            }
        }
        if f.is_null() {
            eprintln!("no foreign function `{}`", String::from_utf8_lossy(&name[..end]));
            return None;
        }
        type Given = (usize, usize, usize, usize, usize, usize, f64, f64, f64, f64, f64, f64, f64, f64);
        let g: Given = (
            whole[0], whole[1], whole[2], whole[3], whole[4], whole[5], real[0], real[1], real[2],
            real[3], real[4], real[5], real[6], real[7],
        );
        macro_rules! call {
            ($ret:ty) => {{
                type F = extern "C" fn(
                    usize, usize, usize, usize, usize, usize, f64, f64, f64, f64, f64, f64, f64, f64,
                ) -> $ret;
                std::mem::transmute::<*mut u8, F>(f)(
                    g.0, g.1, g.2, g.3, g.4, g.5, g.6, g.7, g.8, g.9, g.10, g.11, g.12, g.13,
                )
            }};
        }
        match width {
            1000 => u128::from(call!(f64).to_bits()),
            1001 => u128::from(call!(f32).to_bits()),
            _ => call!(usize) as u128,
        }
    };
    // What C wrote comes before what is written here next.
    // SAFETY: a null stream is every stream.
    unsafe { fflush(std::ptr::null_mut()) };
    Some(match width {
        0 => unit(),
        1000 | 1001 => Value::Int(raw as i128),
        _ => Value::Int(sized(raw, width)),
    })
}

/// What C calls when it calls a callable of the program's: the callable, and
/// how many values it takes.
struct Callback {
    vm: *mut Vm,
    callee: Value,
    arity: usize,
}

/// # Safety
/// Called by the code `callback` writes, while the machine `ctx` names is in
/// a foreign call.
unsafe extern "C" fn called_back(ctx: *const Callback, a: usize, b: usize, c: usize, d: usize, e: usize) -> u64 {
    let cb = &*ctx;
    let vm = &mut *cb.vm;
    let args = [a, b, c, d, e][..cb.arity].iter().map(|x| Value::Int(*x as i128)).collect();
    match vm.call_back(cb.callee.clone(), args) {
        Some(Value::Int(n)) => n as u64,
        Some(_) => 0,
        None => {
            // C cannot be told: there is nowhere to go on from.
            let _ = vm.out.flush();
            eprintln!("the program went wrong in a function C called");
            std::process::exit(2);
        }
    }
}

/// The address of code that C can call with up to five whole numbers, which
/// runs the callable with them and gives back the whole number it gives.
/// Neither the code nor the callable is ever let go of.
fn callback(vm: &mut Vm, callee: Value, arity: usize) -> Step<usize> {
    extern "C" {
        fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    }
    let ctx = Box::into_raw(Box::new(Callback { vm, callee, arity }));
    // The values C gives move over by one, the first becomes `ctx`, and
    // `called_back` is jumped to: mov r9, r8; mov r8, rcx; mov rcx, rdx;
    // mov rdx, rsi; mov rsi, rdi; mov rdi, ctx; mov rax, called_back; jmp rax.
    let mut code: Vec<u8> = vec![
        0x4D, 0x89, 0xC1, 0x49, 0x89, 0xC8, 0x48, 0x89, 0xD1, 0x48, 0x89, 0xF2, 0x48, 0x89, 0xFE, 0x48, 0xBF,
    ];
    code.extend_from_slice(&(ctx as u64).to_le_bytes());
    code.extend_from_slice(&[0x48, 0xB8]);
    code.extend_from_slice(&(called_back as *const () as u64).to_le_bytes());
    code.extend_from_slice(&[0xFF, 0xE0]);
    // SAFETY: a page of its own, readable, writable and executable.
    unsafe {
        let page = mmap(std::ptr::null_mut(), 4096, 7, 0x22, -1, 0);
        if page as isize == -1 {
            return wrong();
        }
        std::ptr::copy_nonoverlapping(code.as_ptr(), page, code.len());
        Ok(page as usize)
    }
}

pub struct Vm {
    codes: Rc<Vec<Vec<Instr>>>,
    functions: usize,
    code: usize,
    pc: usize,
    locals: Vec<Value>,
    frames: Vec<Frame>,
    /// Captured continuations. A resumption is one-shot: resuming or
    /// cancelling it moves its frames out and leaves the entry empty.
    conts: Vec<Option<Vec<Frame>>>,
    /// How many label scopes and handlers have been put on the stack; the
    /// identity of the next one.
    labels: u64,
    /// Memory: a cell is live with a value, or has been freed.
    cells: Vec<Option<Value>>,
    input: VecDeque<i64>,
    out: BufWriter<io::Stdout>,
    names: Vec<String>,
    /// Why the machine stopped, when compiled code was running: it is told
    /// to return, and whoever called it reads this.
    stop: Option<Stop>,
    /// Lists of values no longer in use, emptied, to be used again.
    pool: Vec<Vec<Value>>,
    /// For each function whose closures say how they are destroyed, the
    /// function that destroys what one captured.
    drops: Rc<HashMap<usize, usize>>,
}

impl Vm {
    fn atom(&mut self, a: &Atom) -> Step<Value> {
        match a {
            Atom::Var(i) => self.locals.get(*i).cloned().ok_or(Stop::Wrong),
            Atom::Take(i) => match self.locals.get_mut(*i) {
                Some(slot) => Ok(std::mem::replace(slot, Value::Int(0))),
                None => wrong(),
            },
            Atom::Int(n) => Ok(Value::Int(*n)),
        }
    }

    fn atoms(&mut self, xs: &[Atom]) -> Step<Vec<Value>> {
        let mut out = self.spare(xs.len());
        for a in xs {
            out.push(self.atom(a)?);
        }
        Ok(out)
    }

    /// An empty list of values with room for `n`: one that an activation
    /// that ended had, if there is one, so that a call need not ask for
    /// memory.
    fn spare(&mut self, n: usize) -> Vec<Value> {
        match self.pool.pop() {
            Some(mut v) => {
                v.reserve(n);
                v
            }
            None => Vec::with_capacity(n.max(8)),
        }
    }

    /// The locals of an activation that has ended, kept for the next.
    fn recycle(&mut self, mut v: Vec<Value>) {
        v.clear();
        if self.pool.len() < 64 {
            self.pool.push(v);
        }
    }

    fn place(&self, pl: &Place) -> Step<Value> {
        let mut v = self.locals.get(pl.var).ok_or(Stop::Wrong)?;
        for &i in &pl.path {
            match v {
                Value::Data(d) => v = d.fields.get(i).ok_or(Stop::Wrong)?,
                _ => return wrong(),
            }
        }
        Ok(v.clone())
    }

    fn rhs(&mut self, r: &Rhs) -> Step<Value> {
        match r {
            Rhs::Atom(a) => self.atom(a),
            Rhs::Prim(p, args) => {
                let args = self.atoms(args)?;
                match p {
                    Prim::ArrGet | Prim::ArrSet | Prim::ArrLen | Prim::ArrPush | Prim::ArrPop => {
                        array_prim(*p, args)
                    }
                    _ => prim(*p, &args),
                }
            }
            Rhs::Construct(tag, args) => Ok(data(*tag, self.atoms(args)?)),
            Rhs::Place(pl) => self.place(pl),
            Rhs::Closure(func, caps) => {
                Ok(Value::Clo(Rc::new(Clo { func: *func, caps: self.atoms(caps)? })))
            }
            Rhs::Rebind(a, func) => match self.atom(a)? {
                Value::Clo(clo) => {
                    Ok(Value::Clo(Rc::new(Clo { func: *func, caps: clo.caps.clone() })))
                }
                _ => Err(Stop::Wrong),
            },
        }
    }

    /// Enter a function: its locals are the arguments followed by the captures.
    fn call_fn(&mut self, func: usize, caps: &[Value], mut args: Vec<Value>) -> Step<()> {
        if func >= self.functions {
            return wrong();
        }
        args.extend_from_slice(caps);
        self.code = func;
        self.pc = 0;
        let ended = std::mem::replace(&mut self.locals, args);
        self.recycle(ended);
        Ok(())
    }

    /// Deliver a result to the top of the stack.
    fn deliver(&mut self, mut v: Value) -> Step<()> {
        loop {
            match self.frames.pop() {
                None => return Err(Stop::Halt(v)),
                Some(Frame::Ret { code, pc, mut locals }) => {
                    locals.push(v);
                    self.code = code;
                    self.pc = pc;
                    let ended = std::mem::replace(&mut self.locals, locals);
                    self.recycle(ended);
                    return Ok(());
                }
                Some(Frame::Handler { handler, .. }) => {
                    return self.call_fn(handler.ret, &handler.caps, vec![v]);
                }
                Some(Frame::Label(_)) => {}
                Some(Frame::Guard { func, caps }) => {
                    self.frames.push(Frame::Yield(v));
                    return self.call_fn(func, &caps, Vec::new());
                }
                Some(Frame::Cell(addr)) => self.release(addr),
                Some(Frame::Yield(w)) => v = w,
                Some(Frame::Exit { target, after }) => return self.leave(target, after),
                Some(Frame::Boundary) => return Err(Stop::Back(v)),
            }
        }
    }

    /// Leave for `target`, abandoning the frames on the way. Each cleanup among
    /// them runs in place, with everything below it still there; when it is
    /// done the exit goes on. Once the target is reached it is removed and
    /// `after` happens on what is below it.
    fn leave(&mut self, target: Target, after: After) -> Step<()> {
        loop {
            let frame = self.frames.pop().ok_or(Stop::Wrong)?;
            if frame.is_target(target) {
                return match after {
                    After::Yield(v) => self.deliver(v),
                    After::Invoke { func, caps, args } => self.call_fn(func, &caps, args),
                };
            }
            match frame {
                Frame::Guard { func, caps } => {
                    self.frames.push(Frame::Exit { target, after });
                    return self.call_fn(func, &caps, Vec::new());
                }
                Frame::Cell(addr) => self.release(addr),
                // An exit does not pass a foreign function.
                Frame::Boundary => return wrong(),
                _ => {}
            }
        }
    }

    /// Run a callable to its result while a foreign function waits for it:
    /// the activation that called the foreign function is set aside and
    /// taken up again as it was.
    fn call_back(&mut self, callee: Value, args: Vec<Value>) -> Option<Value> {
        let (code, pc) = (self.code, self.pc);
        let locals = std::mem::take(&mut self.locals);
        let depth = self.frames.len();
        self.frames.push(Frame::Boundary);
        let mut step = self.apply(callee, args);
        while step.is_ok() {
            step = self.step();
        }
        self.frames.truncate(depth);
        self.code = code;
        self.pc = pc;
        self.locals = locals;
        match step {
            Err(Stop::Back(v)) => Some(v),
            _ => None,
        }
    }

    /// The scope of a cell has ended: the cell is released.
    fn release(&mut self, addr: usize) {
        if let Some(cell) = self.cells.get_mut(addr) {
            *cell = None;
        }
    }

    /// Apply a callee: enter a function, resume a continuation, or leave a label scope.
    fn apply(&mut self, callee: Value, mut args: Vec<Value>) -> Step<()> {
        match callee {
            Value::Clo(c) => self.call_fn(c.func, &c.caps, args),
            Value::Cont(id) => {
                if args.len() != 1 {
                    return wrong();
                }
                let segment = self.conts.get_mut(id).and_then(Option::take).ok_or(Stop::Wrong)?;
                self.frames.extend(segment);
                self.deliver(args.pop().unwrap())
            }
            Value::Label(id) => {
                if args.len() != 1 {
                    return wrong();
                }
                if !self.frames.iter().any(|f| f.is_target(Target::Label(id))) {
                    return wrong();
                }
                self.leave(Target::Label(id), After::Yield(args.pop().unwrap()))
            }
            _ => wrong(),
        }
    }

    /// The nearest handler with an arm for `op`: its position, its identity,
    /// the handler, the arm.
    fn find_handler(&self, op: u64) -> Step<(usize, u64, Rc<Handler>, usize)> {
        for (at, frame) in self.frames.iter().enumerate().rev() {
            // An effect does not pass a foreign function.
            if matches!(frame, Frame::Boundary) {
                break;
            }
            if let Frame::Handler { id, handler } = frame {
                if let Some(&(_, arm)) = handler.ops.iter().find(|(o, _)| *o == op) {
                    return Ok((at, *id, Rc::clone(handler), arm));
                }
            }
        }
        wrong()
    }

    /// A live cell, or nothing if the address is unknown or freed.
    fn cell(&mut self, addr: usize) -> Step<&mut Option<Value>> {
        match self.cells.get_mut(addr) {
            Some(cell) if cell.is_some() => Ok(cell),
            _ => wrong(),
        }
    }

    fn mem(&mut self, op: MemOp, mut args: Vec<Value>) -> Step<Value> {
        match (op, args.as_mut_slice()) {
            (MemOp::Load, [Value::Ref(a, p)]) => {
                let (addr, p) = (*a, p.clone());
                let whole = self.cell(addr)?.as_ref().ok_or(Stop::Wrong)?;
                Ok(part(whole, steps(&p))?.clone())
            }
            (MemOp::Store, [Value::Ref(a, p), _]) => {
                let (addr, p) = (*a, p.clone());
                let new = args.pop().ok_or(Stop::Wrong)?;
                let whole = self.cell(addr)?.as_mut().ok_or(Stop::Wrong)?;
                *part_mut(whole, steps(&p))? = new;
                Ok(unit())
            }
            (MemOp::Swap, [Value::Ref(a, p), _]) => {
                // The old value is moved out, not copied.
                let (addr, p) = (*a, p.clone());
                let new = args.pop().ok_or(Stop::Wrong)?;
                let whole = self.cell(addr)?.as_mut().ok_or(Stop::Wrong)?;
                Ok(std::mem::replace(part_mut(whole, steps(&p))?, new))
            }
            (MemOp::Focus, [Value::Ref(a, p), Value::Int(i)]) => {
                if *i < 0 {
                    return wrong();
                }
                let i = usize::try_from(*i).unwrap_or(usize::MAX);
                let mut path = steps(p).to_vec();
                path.push((0, i));
                Ok(Value::Ref(*a, Some(path.into())))
            }
            // A field of one of a type's several constructors: the step
            // says which, and leads nowhere in a value built by another.
            (MemOp::Focus, [Value::Ref(a, p), Value::Int(i), Value::Int(built)]) => {
                if *i < 0 || *built < 0 {
                    return wrong();
                }
                let i = usize::try_from(*i).unwrap_or(usize::MAX);
                let mut path = steps(p).to_vec();
                path.push((*built as u64 + 1, i));
                Ok(Value::Ref(*a, Some(path.into())))
            }
            (MemOp::Tag, [Value::Ref(a, p), ..]) => {
                // Which constructor built what the reference is to, or the
                // field a path of field numbers leads to; -1 where it leads
                // nowhere.
                let (addr, p) = (*a, p.clone());
                let path: Vec<Value> = args.drain(1..).collect();
                let whole = self.cell(addr)?.as_ref().ok_or(Stop::Wrong)?;
                let mut at = part(whole, steps(&p))?;
                for step in &path {
                    let next = match (at, step) {
                        (Value::Data(d), Value::Int(i)) => {
                            usize::try_from(*i).ok().and_then(|i| d.fields.get(i))
                        }
                        _ => None,
                    };
                    match next {
                        Some(v) => at = v,
                        None => return Ok(Value::Int(-1)),
                    }
                }
                Ok(match at {
                    Value::Data(d) => Value::Int(i128::from(d.tag)),
                    _ => Value::Int(-1),
                })
            }
            _ => wrong(),
        }
    }

    fn push_ret(&mut self) {
        let locals = std::mem::take(&mut self.locals);
        self.frames.push(Frame::Ret { code: self.code, pc: self.pc + 1, locals });
    }

    fn step(&mut self) -> Step<()> {
        // The code outlives the step: nothing a step does lets go of it.
        let codes: &Vec<Vec<Instr>> = unsafe { &*Rc::as_ptr(&self.codes) };
        let instr = codes[self.code].get(self.pc).ok_or(Stop::Wrong)?;
        match instr {
            Instr::Op(r) => {
                let v = self.rhs(r)?;
                self.locals.push(v);
                self.pc += 1;
                Ok(())
            }
            Instr::Call(f, args) => {
                let callee = self.atom(f)?;
                let args = self.atoms(args)?;
                self.push_ret();
                self.apply(callee, args)
            }
            Instr::Tail(f, args) => {
                let callee = self.atom(f)?;
                let args = self.atoms(args)?;
                self.apply(callee, args)
            }
            Instr::CallFn(f, given) => {
                let given = self.atoms(given)?;
                self.push_ret();
                self.call_fn(*f, &[], given)
            }
            Instr::TailFn(f, given) => {
                let given = self.atoms(given)?;
                self.call_fn(*f, &[], given)
            }
            Instr::Jump(t) => {
                self.pc = *t;
                Ok(())
            }
            Instr::Stuck => wrong(),
            Instr::Enter { ret, ops, caps } => {
                let caps = self.atoms(caps)?;
                let handler = Rc::new(Handler { ret: *ret, ops: ops.clone(), caps });
                let id = self.labels;
                self.labels += 1;
                self.frames.push(Frame::Handler { id, handler });
                self.pc += 1;
                Ok(())
            }
            Instr::Again(to, keep) => {
                self.locals.truncate(*keep);
                self.pc = *to;
                Ok(())
            }
            Instr::Leave => match self.frames.pop() {
                Some(Frame::Handler { .. }) => {
                    self.pc += 1;
                    Ok(())
                }
                _ => wrong(),
            },
            Instr::Ret(a) => {
                let v = self.atom(a)?;
                self.deliver(v)
            }
            Instr::Handle { ret, ops, caps, thunk, tail } => {
                let caps = self.atoms(caps)?;
                let callee = self.atom(thunk)?;
                if !matches!(callee, Value::Clo(_)) {
                    return wrong();
                }
                if !tail {
                    self.push_ret();
                }
                let handler = Rc::new(Handler { ret: *ret, ops: ops.clone(), caps });
                let id = self.labels;
                self.labels += 1;
                self.frames.push(Frame::Handler { id, handler });
                self.apply(callee, Vec::new())
            }
            Instr::Raise(op, args) => {
                let args = self.atoms(args)?;
                let (_, id, handler, arm) = self.find_handler(*op)?;
                // The arm runs once the abandoned frames are cleaned up, and
                // outside the handler.
                let after = After::Invoke { func: arm, caps: handler.caps.clone(), args };
                self.leave(Target::Handler(id), after)
            }
            Instr::Perform(op, args) => {
                let mut args = self.atoms(args)?;
                let (at, _, handler, arm) = self.find_handler(*op)?;
                // The continuation runs from the handler up to the performer.
                let mut segment = self.frames.split_off(at);
                let locals = std::mem::take(&mut self.locals);
                segment.push(Frame::Ret { code: self.code, pc: self.pc + 1, locals });
                args.push(Value::Cont(self.conts.len()));
                self.conts.push(Some(segment));
                self.call_fn(arm, &handler.caps, args)
            }
            Instr::Label { thunk, tail } => {
                // Any callable taking one value will do; `apply` rejects the rest.
                let callee = self.atom(thunk)?;
                if !tail {
                    self.push_ret();
                }
                let id = self.labels;
                self.labels += 1;
                self.frames.push(Frame::Label(id));
                self.apply(callee, vec![Value::Label(id)])
            }
            Instr::Guard { cleanup, thunk, tail } => {
                let Value::Clo(c) = self.atom(cleanup)? else {
                    return wrong();
                };
                let callee = self.atom(thunk)?;
                if !matches!(callee, Value::Clo(_)) {
                    return wrong();
                }
                if !tail {
                    self.push_ret();
                }
                self.frames.push(Frame::Guard { func: c.func, caps: c.caps.clone() });
                self.apply(callee, Vec::new())
            }
            Instr::Cell { init, thunk, tail } => {
                let value = self.atom(init)?;
                // Any callable taking one value will do; `apply` rejects the rest.
                let callee = self.atom(thunk)?;
                if !tail {
                    self.push_ret();
                }
                let addr = self.cells.len();
                self.cells.push(Some(value));
                self.frames.push(Frame::Cell(addr));
                self.apply(callee, vec![Value::Ref(addr, None)])
            }
            Instr::Lend { r, thunk, pre, post } => {
                let Value::Ref(addr, path) = self.atom(r)? else {
                    return wrong();
                };
                // A call, with the borrow between the other arguments.
                let callee = self.atom(thunk)?;
                let mut args = self.atoms(pre)?;
                args.push(Value::Ref(addr, path));
                args.extend(self.atoms(post)?);
                self.push_ret();
                // A borrow has an identity, as a label has. Nothing here looks
                // at it, but it is taken from the same counter. The scope of
                // the borrow is a frame only in Core, where it is what the
                // proof about borrows reads; here it would do nothing.
                self.labels += 1;
                self.apply(callee, args)
            }
            Instr::Cancel(k) => {
                let id = match self.atom(k)? {
                    Value::Cont(id) => id,
                    // A closure of a function that says how it is destroyed
                    // gives what it captured to the function that does so,
                    // as a call whose result is the result of `cancel`.
                    Value::Clo(c) if self.drops.contains_key(&c.func) => {
                        let d = self.drops[&c.func];
                        let caps = c.caps.to_vec();
                        self.push_ret();
                        return self.call_fn(d, &[], caps);
                    }
                    // Giving up any other function or a label needs nothing done.
                    Value::Clo(_) | Value::Label(_) => {
                        self.locals.push(unit());
                        self.pc += 1;
                        return Ok(());
                    }
                    _ => return wrong(),
                };
                let segment = self.conts.get_mut(id).and_then(Option::take).ok_or(Stop::Wrong)?;
                // The captured computation is put back inside a fresh label
                // scope and that scope is left at once, so that its cleanups
                // run. Whatever it might still deliver is discarded.
                let scope = self.labels;
                self.labels += 1;
                self.push_ret();
                self.frames.push(Frame::Label(scope));
                self.frames.push(Frame::Yield(unit()));
                self.frames.extend(segment);
                self.leave(Target::Label(scope), After::Yield(unit()))
            }
            Instr::Host(id, args) => {
                let args = self.atoms(args)?;
                let result = match (*id, args.as_slice()) {
                    (0, [v]) => {
                        let line = show(&self.names, v);
                        writeln!(self.out, "{line}").expect("cannot write to standard output");
                        unit()
                    }
                    (1, []) => match self.input.pop_front() {
                        Some(n) => data(0, vec![Value::Int(1), Value::Int(i128::from(n))]),
                        None => data(0, vec![Value::Int(0), Value::Int(0)]),
                    },
                    // What is unsafe. The proved machines give these no meaning.
                    (2, vs) => {
                        // What C writes comes after what was written here.
                        self.out.flush().expect("cannot write to standard output");
                        foreign_call(vs).ok_or(Stop::Wrong)?
                    }
                    (3, [Value::Int(at), Value::Int(width)]) => {
                        Value::Int(sized(read_at(*at as usize, width.unsigned_abs() as usize / 8), *width))
                    }
                    (4, [Value::Int(at), Value::Int(width), Value::Int(v)]) => {
                        write_at(*at as usize, width.unsigned_abs() as usize / 8, *v as u128);
                        unit()
                    }
                    // An address C can call, which runs a callable of so
                    // many whole numbers that gives one.
                    (5, [callee, Value::Int(arity)]) if (0..=5).contains(arity) => {
                        Value::Int(callback(self, callee.clone(), *arity as usize)? as i128)
                    }
                    _ => return wrong(),
                };
                self.locals.push(result);
                self.pc += 1;
                Ok(())
            }
            Instr::TestCtor(pl, tag, arity, fail) => {
                let holds = match self.place(pl)? {
                    Value::Data(d) => d.tag == *tag && d.fields.len() == *arity,
                    _ => false,
                };
                self.pc = if holds { self.pc + 1 } else { *fail };
                Ok(())
            }
            Instr::TestInt(pl, n, fail) => {
                let holds = matches!(self.place(pl)?, Value::Int(m) if m == *n);
                self.pc = if holds { self.pc + 1 } else { *fail };
                Ok(())
            }
            Instr::Mem(op, args) => {
                let args = self.atoms(args)?;
                let result = self.mem(*op, args)?;
                self.locals.push(result);
                self.pc += 1;
                Ok(())
            }
        }
    }
}

/// Intrinsics. An integer is held in 128 bits. The arithmetic of `Int` is
/// kept to 64; the wide and the unsigned operations to 128.
/// The fields of a value made of fields, to change: the value's own if
/// nothing else holds it, else a copy.
fn fields_of(d: Rc<Data>) -> (u64, Vec<Value>) {
    match Rc::try_unwrap(d) {
        Ok(d) => (d.tag, d.fields),
        Err(d) => (d.tag, d.fields.clone()),
    }
}

/// The intrinsics of arrays: a value made of fields, read and changed at a
/// place.
fn array_prim(p: Prim, args: Vec<Value>) -> Step<Value> {
    let mut args = args.into_iter();
    let Some(Value::Data(d)) = args.next() else {
        return wrong();
    };
    match (p, args.next(), args.next()) {
        (Prim::ArrGet, Some(Value::Int(i)), None) => {
            usize::try_from(i).ok().and_then(|i| d.fields.get(i).cloned()).ok_or(Stop::Wrong)
        }
        (Prim::ArrSet, Some(Value::Int(i)), Some(v)) => {
            let i = usize::try_from(i).ok().filter(|i| *i < d.fields.len()).ok_or(Stop::Wrong)?;
            let (tag, mut fields) = fields_of(d);
            fields[i] = v;
            Ok(data(tag, fields))
        }
        (Prim::ArrLen, Some(_), None) => Ok(Value::Int(d.fields.len() as i128)),
        (Prim::ArrPush, Some(v), None) => {
            let (tag, mut fields) = fields_of(d);
            fields.push(v);
            Ok(data(tag + 1, fields))
        }
        (Prim::ArrPop, Some(_), None) => {
            let (tag, mut fields) = fields_of(d);
            let last = fields.pop().ok_or(Stop::Wrong)?;
            Ok(data(0, vec![data(tag.wrapping_sub(1), fields), last]))
        }
        _ => wrong(),
    }
}

fn prim(p: Prim, args: &[Value]) -> Step<Value> {
    let [Value::Int(a), Value::Int(b)] = args else {
        return wrong();
    };
    let (a, b) = (*a, *b);
    let narrow = |r: Option<i128>| r.filter(|r| i64::try_from(*r).is_ok());
    let unsigned = |r: Option<u128>| r.map(|r| r as i128);
    let (ua, ub) = (a as u128, b as u128);
    let result = match p {
        Prim::Add => narrow(a.checked_add(b)),
        Prim::Sub => narrow(a.checked_sub(b)),
        Prim::Mul => narrow(a.checked_mul(b)),
        Prim::Lt => Some(i128::from(a < b)),
        Prim::Eq => Some(i128::from(a == b)),
        // Towards zero. The least integer divided by -1 does not fit; what is
        // left of that division is zero.
        Prim::Div => {
            if b == 0 {
                None
            } else {
                a.checked_div(b)
            }
        }
        Prim::Rem => match b {
            0 => None,
            -1 => Some(0),
            _ => a.checked_rem(b),
        },
        Prim::Fit => fits(a, b).then_some(a),
        Prim::FAdd => float2(a, b, |x, y| x + y),
        Prim::FSub => float2(a, b, |x, y| x - y),
        Prim::FMul => float2(a, b, |x, y| x * y),
        Prim::FDiv => float2(a, b, |x, y| x / y),
        Prim::FLt => Some(i128::from(float(a) < float(b))),
        Prim::FEq => Some(i128::from(float(a) == float(b))),
        // The nearest number to an integer of any size: `as` rounds so.
        Prim::FOfInt => Some(bits(a as f64)),
        Prim::FToInt => {
            let whole = float(a).trunc();
            // Both bounds are powers of two, so they are exact.
            (whole >= -9223372036854775808.0 && whole < 9223372036854775808.0)
                .then_some(whole as i128)
        }
        Prim::FNarrow => {
            let narrow = float(a) as f32;
            Some(if narrow.is_nan() {
                0x7FC0_0000
            } else {
                i128::from(narrow.to_bits())
            })
        }
        Prim::FWiden => Some(bits(f64::from(f32::from_bits(ua as u32)))),
        Prim::FOfDecimal => Some(bits(of_decimal(a, b))),
        Prim::FDigits => decimal(a, b).map(|(digits, _)| digits),
        Prim::FExp10 => decimal(a, b).map(|(_, exp10)| exp10),
        Prim::FSqrt => Some(bits(float(a).sqrt())),
        Prim::FRound => match b {
            0 => Some(bits(float(a).floor())),
            1 => Some(bits(float(a).ceil())),
            2 => Some(bits(float(a).trunc())),
            3 => Some(bits(float(a).round_ties_even())),
            _ => None,
        },
        Prim::WAdd => a.checked_add(b),
        Prim::WSub => a.checked_sub(b),
        Prim::WMul => a.checked_mul(b),
        Prim::And => Some(a & b),
        Prim::Or => Some(a | b),
        Prim::Xor => Some(a ^ b),
        // Moved up and back down, an integer is itself only if nothing of
        // it was lost.
        Prim::Shl => (0..128).contains(&b).then(|| a << b).filter(|r| r >> b == a),
        Prim::Shr => {
            if b < 0 {
                None
            } else if b >= 127 {
                Some(if a < 0 { -1 } else { 0 })
            } else {
                Some(a >> b)
            }
        }
        Prim::UAdd => unsigned(ua.checked_add(ub)),
        Prim::USub => unsigned(ua.checked_sub(ub)),
        Prim::UMul => unsigned(ua.checked_mul(ub)),
        Prim::UDiv => unsigned(ua.checked_div(ub)),
        Prim::URem => unsigned(ua.checked_rem(ub)),
        Prim::ULt => Some(i128::from(ua < ub)),
        Prim::UShl => unsigned((0..128).contains(&b).then(|| ua << b).filter(|r| r >> b == ua)),
        Prim::UShr => {
            if b < 0 {
                None
            } else if b >= 128 {
                Some(0)
            } else {
                unsigned(Some(ua >> b))
            }
        }
        Prim::Below => (0 <= a && a < b).then_some(a),
        // Of two integers these have no meaning.
        Prim::ArrGet | Prim::ArrSet | Prim::ArrLen | Prim::ArrPush | Prim::ArrPop => None,
    };
    result.map(Value::Int).ok_or(Stop::Wrong)
}

/// Does an integer fit in a width: so many bits with a sign if the width is
/// positive, without one if it is negative?
fn fits(a: i128, width: i128) -> bool {
    if width > 0 {
        width >= 128 || (-(1i128 << (width - 1)) <= a && a < (1i128 << (width - 1)))
    } else if width < 0 {
        let width = width.unsigned_abs();
        a >= 0 && (width >= 127 || a < (1i128 << width))
    } else {
        false
    }
}

/// A floating point number is held as the integer with its bits: the low 64
/// of them.
fn float(bits: i128) -> f64 {
    f64::from_bits(bits as u64)
}

/// There is one NaN: quiet, with no sign and no payload. The bits are a
/// 64-bit integer with a sign.
fn bits(x: f64) -> i128 {
    if x.is_nan() {
        0x7FF8_0000_0000_0000
    } else {
        i128::from(x.to_bits() as i64)
    }
}

fn float2(a: i128, b: i128, op: impl Fn(f64, f64) -> f64) -> Option<i128> {
    Some(bits(op(float(a), float(b))))
}

/// `digits * 10^exp10`, to the nearest number.
fn of_decimal(digits: i128, exp10: i128) -> f64 {
    if digits == 0 {
        0.0
    } else if exp10 > 400 {
        if digits < 0 {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        }
    } else if exp10 < -400 {
        if digits < 0 {
            -0.0
        } else {
            0.0
        }
    } else {
        format!("{digits}e{exp10}").parse().unwrap_or(f64::NAN)
    }
}

/// A number to `p` digits, 1 to 17: the digits as an integer, without the
/// sign, and the power of ten they are to be multiplied by. Zero is `(0, 0)`.
fn decimal(a: i128, p: i128) -> Option<(i128, i128)> {
    let x = float(a).abs();
    if !(1..=17).contains(&p) || !x.is_finite() {
        return None;
    }
    if x == 0.0 {
        return Some((0, 0));
    }
    let p = p as usize;
    let text = format!("{:.*e}", p - 1, x);
    let (mantissa, exponent) = text.split_once('e')?;
    let digits: i128 = mantissa.replace('.', "").parse().ok()?;
    let exponent: i128 = exponent.parse().ok()?;
    Some((digits, exponent - (p as i128 - 1)))
}

/// The name a constructor is shown under.
fn ctor_name(names: &[String], tag: u64) -> Option<&str> {
    usize::try_from(tag)
        .ok()
        .and_then(|i| names.get(i))
        .map(String::as_str)
}

/// The characters of a text, if the value is one: the prelude's `Str`, whose
/// constructors are shown under names no program can write.
fn text_of(names: &[String], v: &Value) -> Option<String> {
    let mut out = String::new();
    let mut at = v;
    loop {
        let Value::Data(d) = at else { return None };
        match (ctor_name(names, d.tag as u64)?, d.fields.as_slice()) {
            ("%end", []) => return Some(out),
            ("%char", [Value::Int(code), rest]) => {
                // A code that is no character is U+FFFD.
                out.push(
                    u32::try_from(*code)
                        .ok()
                        .and_then(char::from_u32)
                        .unwrap_or('\u{FFFD}'),
                );
                at = rest;
            }
            _ => return None,
        }
    }
}

/// A text inside another value: in quotes.
fn quoted(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A value as it is shown. A text is shown as its characters; inside another
/// value, in quotes.
fn show(names: &[String], v: &Value) -> String {
    match text_of(names, v) {
        Some(text) => text,
        None => show_inner(names, v),
    }
}

fn show_inner(names: &[String], v: &Value) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Data(d) => {
            if let Some(text) = text_of(names, v) {
                return quoted(&text);
            }
            let args: Vec<String> = d.fields.iter().map(|f| show_inner(names, f)).collect();
            let args = args.join(", ");
            if d.tag == 0 {
                return format!("({args})");
            }
            // The constructors that build arrays are above every declared one.
            if d.tag >= 4611686018427387904 {
                return format!("[{args}]");
            }
            let name = usize::try_from(d.tag)
                .ok()
                .and_then(|i| names.get(i).cloned())
                .unwrap_or_else(|| format!("#{}", d.tag));
            if d.fields.is_empty() {
                name
            } else {
                format!("{name}({args})")
            }
        }
        Value::Clo(c) => format!("<fn {}>", c.func),
        Value::Cont(id) => format!("<resumption {id}>"),
        Value::Label(id) => format!("<label {id}>"),
        Value::Ref(addr, _) => format!("<ref {addr}>"),
    }
}

/// How a function is run: by the interpreter, or by code compiled for it.
#[derive(Clone, Copy, PartialEq)]
enum Backend {
    Interp,
    X86,
    /// Every third function interpreted, the rest compiled: what shows that
    /// the two call each other.
    Mix,
}

fn machine(program: Program, input: VecDeque<i64>) -> Vm {
    let functions = program.codes.len();
    Vm {
        codes: Rc::new(program.codes),
        functions,
        code: program.main,
        pc: 0,
        locals: Vec::new(),
        frames: Vec::new(),
        conts: Vec::new(),
        labels: 0,
        cells: Vec::new(),
        input,
        out: BufWriter::new(io::stdout()),
        names: program.names,
        stop: None,
        pool: Vec::new(),
        drops: Rc::new(program.drops),
    }
}

/// Run to the end and say how it ended, as the process's exit code.
fn finish(vm: &mut Vm, bodies: &[Option<native::Body>]) -> u8 {
    match vm.run(bodies) {
        Stop::Halt(v) => {
            let line = show(&vm.names, &v);
            writeln!(vm.out, "{line}").expect("cannot write to standard output");
            vm.out.flush().expect("cannot write to standard output");
            0
        }
        Stop::Wrong | Stop::Back(_) => {
            vm.out.flush().expect("cannot write to standard output");
            eprintln!("the program went wrong");
            2
        }
    }
}

fn inputs(rest: &[String]) -> Result<VecDeque<i64>, String> {
    let mut input = VecDeque::new();
    for a in rest {
        match a.parse::<i64>() {
            Ok(n) => input.push_back(n),
            Err(_) => return Err(format!("input `{a}` is not a 64-bit integer")),
        }
    }
    Ok(input)
}

/// What marks a program put at the end of this executable, before its length.
const BUNDLE: &[u8; 8] = b"GLBUNDLE";

/// The program at the end of this executable, if one was put there, and how
/// long the executable is without it.
fn bundled() -> Option<(Vec<u8>, u64)> {
    use std::io::{Read, Seek, SeekFrom};
    let mut file = std::fs::File::open(std::env::current_exe().ok()?).ok()?;
    let size = file.metadata().ok()?.len();
    if size < 16 {
        return None;
    }
    let mut tail = [0u8; 16];
    file.seek(SeekFrom::Start(size - 16)).ok()?;
    file.read_exact(&mut tail).ok()?;
    if &tail[..8] != BUNDLE {
        return None;
    }
    let length = u64::from_le_bytes(tail[8..].try_into().ok()?);
    let start = size.checked_sub(16 + length)?;
    let mut bytes = vec![0u8; length as usize];
    file.seek(SeekFrom::Start(start)).ok()?;
    file.read_exact(&mut bytes).ok()?;
    Some((bytes, start))
}

/// Write an executable that is this one with a program at its end: run, it
/// runs the program, compiled when it starts.
fn bundle(program: &[u8], out: &str) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let mut exe = std::fs::read(std::env::current_exe()?)?;
    if let Some((_, own)) = bundled() {
        exe.truncate(own as usize);
    }
    exe.extend_from_slice(program);
    exe.extend_from_slice(BUNDLE);
    exe.extend_from_slice(&(program.len() as u64).to_le_bytes());
    std::fs::write(out, exe)?;
    std::fs::set_permissions(out, std::fs::Permissions::from_mode(0o755))
}

pub fn cli_main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // An executable with a program at its end is that program: what it is
    // given is the program's input.
    if let Some((bytes, _)) = bundled() {
        let input = match inputs(&args) {
            Ok(input) => input,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::from(64);
            }
        };
        let rewrite = std::env::var("GLORIOUS_OPT").as_deref() != Ok("0");
        let program = match decode(&bytes, rewrite) {
            Ok(program) => program,
            Err(e) => {
                eprintln!("{e}");
                return ExitCode::from(1);
            }
        };
        let bodies = match std::env::var("GLORIOUS_BACKEND").as_deref() {
            Ok("interp") => Vec::new(),
            Ok("mix") => x86::compile(&program.codes, |f| f % 3 != 1),
            _ => x86::compile(&program.codes, |_| true),
        };
        let mut vm = machine(program, input);
        return ExitCode::from(finish(&mut vm, &bodies));
    }
    // Compiled where there is a backend for the machine, unless told otherwise.
    let mut backend = match std::env::var("GLORIOUS_BACKEND").as_deref() {
        Ok("x86") => Backend::X86,
        Ok("mix") => Backend::Mix,
        Ok("interp") => Backend::Interp,
        _ if cfg!(all(target_arch = "x86_64", target_os = "linux")) => Backend::X86,
        _ => Backend::Interp,
    };
    let mut emit = false;
    let mut bundling = false;
    let mut dump = false;
    let mut rewrite = std::env::var("GLORIOUS_OPT").as_deref() != Ok("0");
    while let Some(first) = args.first() {
        match first.as_str() {
            "--backend=interp" => backend = Backend::Interp,
            "--backend=x86" => backend = Backend::X86,
            "--backend=mix" => backend = Backend::Mix,
            "--emit-llvm" => emit = true,
            "--bundle" => bundling = true,
            "--dump" => dump = true,
            "--no-opt" => rewrite = false,
            _ => break,
        }
        args.remove(0);
    }
    let Some((path, rest)) = args.split_first() else {
        eprintln!("usage: glorious-vm [--backend=interp|x86|mix] [--no-opt] [--emit-llvm] [--dump] FILE [INPUT...]\n       glorious-vm --bundle FILE OUT");
        return ExitCode::from(64);
    };
    // (What follows the file is the program's input, or where to write.)
    let input = match inputs(if bundling { &[] } else { rest }) {
        Ok(input) => input,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(64);
        }
    };
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("{path}: {e}");
            return ExitCode::from(1);
        }
    };
    if bundling {
        // `--bundle FILE OUT`: an executable of the program's own, written
        // here with no other tool.
        let Some(out) = rest.first() else {
            eprintln!("usage: glorious-vm --bundle FILE OUT");
            return ExitCode::from(64);
        };
        if let Err(e) = decode(&bytes, false) {
            eprintln!("{path}: {e}");
            return ExitCode::from(1);
        }
        return match bundle(&bytes, out) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("{out}: {e}");
                ExitCode::from(1)
            }
        };
    }
    let program = match decode(&bytes, rewrite) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{path}: {e}");
            return ExitCode::from(1);
        }
    };
    if dump {
        // The instructions as they were read, for whoever works on a backend.
        for (f, code) in program.codes.iter().enumerate() {
            println!("function {f} starts {:?}", program.starts[f]);
            for (pc, instr) in code.iter().enumerate() {
                println!("  {pc}: {instr:?}");
            }
        }
        return ExitCode::SUCCESS;
    }
    if emit {
        print!("{}", llvm::emit(&program, &bytes, rewrite));
        return ExitCode::SUCCESS;
    }
    let bodies: Vec<Option<native::Body>> = match backend {
        Backend::Interp => Vec::new(),
        Backend::X86 => x86::compile(&program.codes, |_| true),
        Backend::Mix => x86::compile(&program.codes, |f| f % 3 != 1),
    };
    let mut vm = machine(program, input);
    ExitCode::from(finish(&mut vm, &bodies))
}

mod llvm;
mod native;
mod opt;
mod x86;
