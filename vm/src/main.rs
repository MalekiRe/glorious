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

use std::collections::VecDeque;
use std::io::{self, BufWriter, Write};
use std::process::ExitCode;
use std::rc::Rc;

// ---------------------------------------------------------------- values

#[derive(Clone)]
enum Value {
    Int(i64),
    Data(Rc<Data>),
    Clo(Rc<Clo>),
    Cont(usize),
    Label(u64),
    Ref(usize),
}

struct Data {
    tag: u64,
    fields: Vec<Value>,
}

struct Clo {
    func: usize,
    caps: Vec<Value>,
}

fn data(tag: u64, fields: Vec<Value>) -> Value {
    Value::Data(Rc::new(Data { tag, fields }))
}

fn unit() -> Value {
    data(0, Vec::new())
}

// ---------------------------------------------------------------- code

enum Atom {
    Var(usize),
    Int(i64),
}

struct Place {
    var: usize,
    path: Vec<usize>,
}

#[derive(Clone, Copy)]
enum Prim {
    Add,
    Sub,
    Mul,
    Lt,
    Eq,
}

#[derive(Clone, Copy)]
enum MemOp {
    Alloc,
    Load,
    Store,
    Free,
}

enum Rhs {
    Atom(Atom),
    Prim(Prim, Vec<Atom>),
    Construct(u64, Vec<Atom>),
    Place(Place),
    Closure(usize, Vec<Atom>),
}

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
    TestInt(Place, i64, usize),
    Mem(MemOp, Vec<Atom>),
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

    /// Zigzag: `2m` is `m`, `2m + 1` is `-(m + 1)`.
    fn int(&mut self) -> Decoded<i64> {
        let z = self.nat()?;
        let half = (z >> 1) as i64;
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
                    0 => MemOp::Alloc,
                    1 => MemOp::Load,
                    2 => MemOp::Store,
                    3 => MemOp::Free,
                    t => return Err(format!("unknown memory operation {t}")),
                };
                Ok(Instr::Mem(op, self.atoms()?))
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

struct Program {
    names: Vec<String>,
    /// The functions, followed by the main code.
    codes: Vec<Vec<Instr>>,
}

fn decode(bytes: &[u8]) -> Decoded<Program> {
    if bytes.len() < 5 || &bytes[..4] != b"GLBC" {
        return Err("not a Glorious bytecode file".into());
    }
    if bytes[4] != 1 {
        return Err(format!("unsupported bytecode version {}", bytes[4]));
    }
    let mut r = Reader { bytes, pos: 5 };
    let names = r.list(Reader::string)?;
    let mut codes = r.list(Reader::code)?;
    codes.push(r.code()?);
    if r.pos != bytes.len() {
        return Err("trailing bytes after the program".into());
    }
    Ok(Program { names, codes })
}

// ---------------------------------------------------------------- machine

struct Handler {
    ret: usize,
    ops: Vec<(u64, usize)>,
    caps: Vec<Value>,
}

enum Frame {
    /// Where to continue after a call returns, and the locals to restore.
    Ret { code: usize, pc: usize, locals: Vec<Value> },
    /// The delimiter of an installed handler.
    Handler(Rc<Handler>),
    /// The scope of a label.
    Label(u64),
    /// A cleanup that runs when the computation above it is left.
    Guard { func: usize, caps: Vec<Value> },
    /// A pending call: what is delivered here is discarded and the function runs.
    Invoke { func: usize, caps: Vec<Value>, args: Vec<Value> },
    /// A pending result: what is delivered here is discarded and this is delivered.
    Yield(Value),
}

/// Why the machine stopped.
enum Stop {
    Halt(Value),
    Wrong,
}

type Step<T> = Result<T, Stop>;

fn wrong<T>() -> Step<T> {
    Err(Stop::Wrong)
}

struct Vm {
    codes: Rc<Vec<Vec<Instr>>>,
    functions: usize,
    code: usize,
    pc: usize,
    locals: Vec<Value>,
    frames: Vec<Frame>,
    conts: Vec<Option<Vec<Frame>>>,
    labels: u64,
    /// Memory: a cell is live with a value, or has been freed.
    cells: Vec<Option<Value>>,
    input: VecDeque<i64>,
    out: BufWriter<io::Stdout>,
    names: Vec<String>,
}

impl Vm {
    fn atom(&self, a: &Atom) -> Step<Value> {
        match a {
            Atom::Var(i) => self.locals.get(*i).cloned().ok_or(Stop::Wrong),
            Atom::Int(n) => Ok(Value::Int(*n)),
        }
    }

    fn atoms(&self, xs: &[Atom]) -> Step<Vec<Value>> {
        xs.iter().map(|a| self.atom(a)).collect()
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

    fn rhs(&self, r: &Rhs) -> Step<Value> {
        match r {
            Rhs::Atom(a) => self.atom(a),
            Rhs::Prim(p, args) => prim(*p, &self.atoms(args)?),
            Rhs::Construct(tag, args) => Ok(data(*tag, self.atoms(args)?)),
            Rhs::Place(pl) => self.place(pl),
            Rhs::Closure(func, caps) => {
                Ok(Value::Clo(Rc::new(Clo { func: *func, caps: self.atoms(caps)? })))
            }
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
        self.locals = args;
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
                    self.locals = locals;
                    return Ok(());
                }
                Some(Frame::Handler(h)) => return self.call_fn(h.ret, &h.caps, vec![v]),
                Some(Frame::Label(_)) => {}
                Some(Frame::Guard { func, caps }) => {
                    self.frames.push(Frame::Yield(v));
                    return self.call_fn(func, &caps, Vec::new());
                }
                Some(Frame::Invoke { func, caps, args }) => return self.call_fn(func, &caps, args),
                Some(Frame::Yield(w)) => v = w,
            }
        }
    }

    /// Turn the guards of abandoned frames into pending cleanup calls, so the
    /// innermost cleanup ends up on top. `abandoned` is bottom first.
    fn push_cleanups(&mut self, abandoned: Vec<Frame>, skip: usize) {
        for frame in abandoned.into_iter().skip(skip) {
            if let Frame::Guard { func, caps } = frame {
                self.frames.push(Frame::Invoke { func, caps, args: Vec::new() });
            }
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
                let at = self
                    .frames
                    .iter()
                    .rposition(|f| matches!(f, Frame::Label(l) if *l == id))
                    .ok_or(Stop::Wrong)?;
                let abandoned = self.frames.split_off(at);
                self.frames.push(Frame::Yield(args.pop().unwrap()));
                self.push_cleanups(abandoned, 1);
                self.deliver(unit())
            }
            _ => wrong(),
        }
    }

    /// The nearest handler with an arm for `op`: its position, the handler, the arm.
    fn find_handler(&self, op: u64) -> Step<(usize, Rc<Handler>, usize)> {
        for (at, frame) in self.frames.iter().enumerate().rev() {
            if let Frame::Handler(h) = frame {
                if let Some(&(_, arm)) = h.ops.iter().find(|(o, _)| *o == op) {
                    return Ok((at, Rc::clone(h), arm));
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
            (MemOp::Alloc, [_]) => {
                self.cells.push(args.pop());
                Ok(Value::Ref(self.cells.len() - 1))
            }
            (MemOp::Load, [Value::Ref(a)]) => Ok(self.cell(*a)?.clone().unwrap()),
            (MemOp::Store, [Value::Ref(a), _]) => {
                let addr = *a;
                *self.cell(addr)? = args.pop();
                Ok(unit())
            }
            (MemOp::Free, [Value::Ref(a)]) => {
                *self.cell(*a)? = None;
                Ok(unit())
            }
            _ => wrong(),
        }
    }

    fn push_ret(&mut self) {
        let locals = std::mem::take(&mut self.locals);
        self.frames.push(Frame::Ret { code: self.code, pc: self.pc + 1, locals });
    }

    fn step(&mut self) -> Step<()> {
        let codes = Rc::clone(&self.codes);
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
                let handler = Handler { ret: *ret, ops: ops.clone(), caps };
                self.frames.push(Frame::Handler(Rc::new(handler)));
                self.apply(callee, Vec::new())
            }
            Instr::Raise(op, args) => {
                let args = self.atoms(args)?;
                let (at, handler, arm) = self.find_handler(*op)?;
                let abandoned = self.frames.split_off(at);
                self.frames.push(Frame::Invoke { func: arm, caps: handler.caps.clone(), args });
                self.push_cleanups(abandoned, 1);
                self.deliver(unit())
            }
            Instr::Perform(op, args) => {
                let mut args = self.atoms(args)?;
                let (at, handler, arm) = self.find_handler(*op)?;
                // The continuation runs from the handler up to the performer.
                let mut segment = self.frames.split_off(at);
                let locals = std::mem::take(&mut self.locals);
                segment.push(Frame::Ret { code: self.code, pc: self.pc + 1, locals });
                args.push(Value::Cont(self.conts.len()));
                self.conts.push(Some(segment));
                self.call_fn(arm, &handler.caps, args)
            }
            Instr::Label { thunk, tail } => {
                let Value::Clo(c) = self.atom(thunk)? else {
                    return wrong();
                };
                if !tail {
                    self.push_ret();
                }
                let id = self.labels;
                self.labels += 1;
                self.frames.push(Frame::Label(id));
                self.call_fn(c.func, &c.caps, vec![Value::Label(id)])
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
            Instr::Cancel(k) => {
                let Value::Cont(id) = self.atom(k)? else {
                    return wrong();
                };
                let segment = self.conts.get_mut(id).and_then(Option::take).ok_or(Stop::Wrong)?;
                self.push_ret();
                self.frames.push(Frame::Yield(unit()));
                self.push_cleanups(segment, 0);
                self.deliver(unit())
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
                        Some(n) => data(0, vec![Value::Int(1), Value::Int(n)]),
                        None => data(0, vec![Value::Int(0), Value::Int(0)]),
                    },
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

/// Intrinsics. Integers are 64-bit and arithmetic is checked.
fn prim(p: Prim, args: &[Value]) -> Step<Value> {
    let [Value::Int(a), Value::Int(b)] = args else {
        return wrong();
    };
    let result = match p {
        Prim::Add => a.checked_add(*b),
        Prim::Sub => a.checked_sub(*b),
        Prim::Mul => a.checked_mul(*b),
        Prim::Lt => Some(i64::from(a < b)),
        Prim::Eq => Some(i64::from(a == b)),
    };
    result.map(Value::Int).ok_or(Stop::Wrong)
}

fn show(names: &[String], v: &Value) -> String {
    match v {
        Value::Int(n) => n.to_string(),
        Value::Data(d) => {
            let args: Vec<String> = d.fields.iter().map(|f| show(names, f)).collect();
            let args = args.join(", ");
            if d.tag == 0 {
                return format!("({args})");
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
        Value::Ref(addr) => format!("<ref {addr}>"),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some((path, rest)) = args.split_first() else {
        eprintln!("usage: glorious-vm FILE [INPUT...]");
        return ExitCode::from(64);
    };
    let mut input = VecDeque::new();
    for a in rest {
        match a.parse::<i64>() {
            Ok(n) => input.push_back(n),
            Err(_) => {
                eprintln!("input `{a}` is not a 64-bit integer");
                return ExitCode::from(64);
            }
        }
    }
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(e) => {
            eprintln!("{path}: {e}");
            return ExitCode::from(1);
        }
    };
    let program = match decode(&bytes) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{path}: {e}");
            return ExitCode::from(1);
        }
    };
    let functions = program.codes.len() - 1;
    let mut vm = Vm {
        codes: Rc::new(program.codes),
        functions,
        code: functions,
        pc: 0,
        locals: Vec::new(),
        frames: Vec::new(),
        conts: Vec::new(),
        labels: 0,
        cells: Vec::new(),
        input,
        out: BufWriter::new(io::stdout()),
        names: program.names,
    };
    loop {
        match vm.step() {
            Ok(()) => {}
            Err(Stop::Halt(v)) => {
                let line = show(&vm.names, &v);
                writeln!(vm.out, "{line}").expect("cannot write to standard output");
                vm.out.flush().expect("cannot write to standard output");
                return ExitCode::SUCCESS;
            }
            Err(Stop::Wrong) => {
                vm.out.flush().expect("cannot write to standard output");
                eprintln!("the program went wrong");
                return ExitCode::from(2);
            }
        }
    }
}
