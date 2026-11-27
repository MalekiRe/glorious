//! A program as it is once loaded: its bytecode rewritten (`opt.rs`), with
//! which readings are moves, written out so that a program built ahead of
//! time starts without rewriting it again. The form is the bytecode file's,
//! with what only a loaded program has: a move (`Atom::Take`, operand tag 2)
//! and the instructions the rewriting writes (tags from 20).

use super::*;

fn nat(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn fields(out: &mut Vec<u8>, fs: &[(usize, Lay)]) {
    nat(out, fs.len() as u64);
    for (off, l) in fs {
        nat(out, *off as u64);
        layout(out, l);
    }
}

fn layout(out: &mut Vec<u8>, l: &Lay) {
    match l {
        Lay::Int(n, signed) => {
            out.push(0);
            nat(out, *n as u64);
            out.push(*signed as u8);
        }
        Lay::Fields(tag, fs) => {
            out.push(1);
            nat(out, *tag);
            fields(out, fs);
        }
        Lay::Tagged(cs) => {
            out.push(2);
            nat(out, cs.len() as u64);
            for (tag, fs) in cs {
                nat(out, *tag);
                fields(out, fs);
            }
        }
        Lay::Addr => out.push(3),
        Lay::Held => out.push(4),
        Lay::Nothing => out.push(5),
    }
}

fn mem_op(out: &mut Vec<u8>, op: &MemOp) {
    let (n, l) = match op {
        MemOp::Load => (0, None),
        MemOp::Store => (1, None),
        MemOp::Swap => (2, None),
        MemOp::Tag => (3, None),
        MemOp::Focus => (4, None),
        MemOp::Alloc => (5, None),
        MemOp::Free => (6, None),
        MemOp::ReadBits => (7, None),
        MemOp::WriteBits => (8, None),
        MemOp::Copy => (9, None),
        MemOp::SizeOf => (15, None),
        MemOp::AlignOf => (16, None),
        MemOp::Deref => (17, None),
        MemOp::StaticAt => (18, None),
        MemOp::AddressOf => (19, None),
        MemOp::LoadL(l) => (10, Some(l)),
        MemOp::StoreL(l) => (11, Some(l)),
        MemOp::SwapL(l) => (12, Some(l)),
        MemOp::TagL(l) => (13, Some(l)),
        MemOp::FocusL(l) => (14, Some(l)),
    };
    out.push(n);
    if let Some(l) = l {
        layout(out, l);
    }
}

fn wide(out: &mut Vec<u8>, mut n: u128) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn int(out: &mut Vec<u8>, n: i128) {
    let z = if n >= 0 { (n as u128) << 1 } else { (((-(n + 1)) as u128) << 1) | 1 };
    wide(out, z);
}

fn atom(out: &mut Vec<u8>, a: &Atom) {
    match a {
        Atom::Var(i) => {
            out.push(0);
            nat(out, *i as u64);
        }
        Atom::Int(n) => {
            out.push(1);
            int(out, *n);
        }
        Atom::Take(i) => {
            out.push(2);
            nat(out, *i as u64);
        }
    }
}

fn atoms(out: &mut Vec<u8>, xs: &[Atom]) {
    nat(out, xs.len() as u64);
    for a in xs {
        atom(out, a);
    }
}

fn place(out: &mut Vec<u8>, pl: &Place) {
    nat(out, pl.var as u64);
    nat(out, pl.path.len() as u64);
    for p in &pl.path {
        nat(out, *p as u64);
    }
}

fn ops(out: &mut Vec<u8>, xs: &[(u64, usize)]) {
    nat(out, xs.len() as u64);
    for (op, f) in xs {
        nat(out, *op);
        nat(out, *f as u64);
    }
}

fn rhs(out: &mut Vec<u8>, r: &Rhs) {
    match r {
        Rhs::Atom(a) => {
            out.push(0);
            atom(out, a);
        }
        Rhs::Prim(p, xs) => {
            out.push(1);
            match p {
                // (Those written with what they are of.)
                Prim::Cast => {
                    out.push(45);
                    int(out, 0);
                    out.push(0);
                }
                Prim::FixedOf => {
                    out.push(46);
                    nat(out, 0);
                }
                Prim::FixedLen => {
                    out.push(46);
                    nat(out, 4);
                }
                p => out.push(*p as u8),
            }
            atoms(out, xs);
        }
        Rhs::Construct(tag, xs) => {
            out.push(2);
            nat(out, *tag);
            atoms(out, xs);
        }
        Rhs::Place(pl) => {
            out.push(3);
            place(out, pl);
        }
        Rhs::Closure(f, xs) => {
            out.push(4);
            nat(out, *f as u64);
            atoms(out, xs);
        }
    }
}

fn instr(out: &mut Vec<u8>, i: &Instr) {
    match i {
        Instr::Op(r) => {
            out.push(0);
            rhs(out, r);
        }
        Instr::Call(f, xs) | Instr::Tail(f, xs) => {
            out.push(if matches!(i, Instr::Call(..)) { 1 } else { 2 });
            atom(out, f);
            atoms(out, xs);
        }
        Instr::Ret(a) => {
            out.push(3);
            atom(out, a);
        }
        Instr::Handle { ret, ops: o, caps, thunk, tail } => {
            out.push(if *tail { 5 } else { 4 });
            nat(out, *ret as u64);
            ops(out, o);
            atoms(out, caps);
            atom(out, thunk);
        }
        Instr::Raise(op, xs) | Instr::Perform(op, xs) | Instr::Host(op, xs) => {
            out.push(match i {
                Instr::Raise(..) => 6,
                Instr::Perform(..) => 7,
                _ => 13,
            });
            nat(out, *op);
            atoms(out, xs);
        }
        Instr::Label { thunk, tail } => {
            out.push(if *tail { 9 } else { 8 });
            atom(out, thunk);
        }
        Instr::Guard { cleanup, thunk, tail } => {
            out.push(if *tail { 11 } else { 10 });
            atom(out, cleanup);
            atom(out, thunk);
        }
        Instr::Cancel(a) => {
            out.push(12);
            atom(out, a);
        }
        Instr::TestCtor(pl, tag, arity, fail) => {
            out.push(14);
            place(out, pl);
            nat(out, *tag);
            nat(out, *arity as u64);
            nat(out, *fail as u64);
        }
        Instr::TestInt(pl, n, fail) => {
            out.push(15);
            place(out, pl);
            int(out, *n);
            nat(out, *fail as u64);
        }
        Instr::Mem(op, xs) => {
            out.push(16);
            mem_op(out, op);
            atoms(out, xs);
        }
        Instr::Cell { init, thunk, tail, lay } => {
            match lay {
                Some(l) => {
                    out.push(if *tail { 21 } else { 20 });
                    nat(out, l.size as u64);
                    nat(out, l.align as u64);
                    layout(out, &l.lay);
                }
                None => out.push(if *tail { 18 } else { 17 }),
            }
            atom(out, init);
            atom(out, thunk);
        }
        Instr::Lend { r, thunk, pre, post } => {
            out.push(19);
            out.push(0);
            atom(out, r);
            atom(out, thunk);
            atoms(out, pre);
            atoms(out, post);
        }
        Instr::CallFn(f, xs) | Instr::TailFn(f, xs) => {
            out.push(if matches!(i, Instr::CallFn(..)) { 20 } else { 21 });
            nat(out, *f as u64);
            atoms(out, xs);
        }
        Instr::Jump(t) => {
            out.push(22);
            nat(out, *t as u64);
        }
        Instr::Stuck => out.push(23),
        Instr::Enter { ret, ops: o, caps } => {
            out.push(24);
            nat(out, *ret as u64);
            ops(out, o);
            atoms(out, caps);
        }
        Instr::Leave => out.push(25),
        Instr::Again(to, keep) => {
            out.push(26);
            nat(out, *to as u64);
            nat(out, *keep as u64);
        }
    }
}

/// What marks a loaded program written out.
pub const MAGIC: &[u8; 6] = b"GLLOAD";

/// A loaded program written out.
pub(crate) fn write(p: &Program) -> Vec<u8> {
    let mut out = MAGIC.to_vec();
    nat(&mut out, p.names.len() as u64);
    for n in &p.names {
        nat(&mut out, n.len() as u64);
        out.extend_from_slice(n.as_bytes());
    }
    nat(&mut out, p.fn_names.len() as u64);
    for n in &p.fn_names {
        nat(&mut out, n.len() as u64);
        out.extend_from_slice(n.as_bytes());
    }
    nat(&mut out, p.codes.len() as u64);
    for code in &p.codes {
        nat(&mut out, code.len() as u64);
        for i in code {
            instr(&mut out, i);
        }
    }
    for s in &p.starts {
        match s {
            Some(n) => nat(&mut out, *n as u64 + 1),
            None => nat(&mut out, 0),
        }
    }
    nat(&mut out, p.main as u64);
    let mut drops: Vec<(&usize, &usize)> = p.drops.iter().collect();
    drops.sort();
    nat(&mut out, drops.len() as u64);
    for (f, d) in drops {
        nat(&mut out, *f as u64);
        nat(&mut out, *d as u64);
    }
    nat(&mut out, p.statics.len() as u64);
    for b in &p.statics {
        nat(&mut out, b.len() as u64);
        for x in b {
            nat(&mut out, *x as u64);
        }
    }
    out
}

impl Reader<'_> {
    fn loaded_instr(&mut self) -> Decoded<Instr> {
        let at = self.pos;
        match self.byte()? {
            20 | 21 => {
                let call = self.bytes[at] == 20;
                let f = self.index()?;
                let xs = self.atoms()?;
                Ok(if call { Instr::CallFn(f, xs) } else { Instr::TailFn(f, xs) })
            }
            22 => Ok(Instr::Jump(self.index()?)),
            23 => Ok(Instr::Stuck),
            24 => {
                let ret = self.index()?;
                let ops = self.list(|r| Ok((r.nat()?, r.index()?)))?;
                let caps = self.atoms()?;
                Ok(Instr::Enter { ret, ops, caps })
            }
            25 => Ok(Instr::Leave),
            26 => {
                let to = self.index()?;
                Ok(Instr::Again(to, self.index()?))
            }
            _ => {
                self.pos = at;
                self.instr()
            }
        }
    }
}

/// A loaded program read back.
pub(crate) fn read(bytes: &[u8]) -> Decoded<Program> {
    if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
        return Err("not a loaded program".into());
    }
    let mut r = Reader { bytes, pos: MAGIC.len(), lays: None };
    let names = r.list(Reader::string)?;
    let fn_names = r.list(Reader::string)?;
    let codes = r.list(|r| r.list(Reader::loaded_instr))?;
    let mut starts = Vec::with_capacity(codes.len());
    for _ in 0..codes.len() {
        let s = r.index()?;
        starts.push(if s == 0 { None } else { Some(s - 1) });
    }
    let main = r.index()?;
    let mut drops = HashMap::new();
    for _ in 0..r.index()? {
        let f = r.index()?;
        drops.insert(f, r.index()?);
    }
    let statics: Vec<Vec<u8>> = r.list(|r| r.list(|r| Ok(r.nat()? as u8)))?;
    let static_at = place_statics(&statics);
    Ok(Program { names, fn_names, codes, starts, main, drops, statics, static_at })
}
