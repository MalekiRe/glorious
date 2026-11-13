//! The x86-64 backend: machine code written straight into memory, with no
//! tool between the bytecode and the processor.
//!
//! It is built to be fast to run, not to make fast code: one pass, a fixed
//! piece of code for each instruction, three registers held throughout.
//! Integers are added, compared and moved in place; everything else is a
//! call into the runtime. The contract is `docs/abi.md`.
//!
//! Registers: `rbx` the machine, `r13` the locals, `r12` how many there are.

use super::*;
use native::{glo_copy, glo_field, glo_is_ctor, glo_step, Body};

extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
}

#[derive(Default)]
struct Asm {
    buf: Vec<u8>,
    /// Where each instruction of the function being compiled starts.
    at: Vec<usize>,
    /// Jumps to an instruction: where the offset is written, and which.
    jumps: Vec<(usize, usize)>,
    /// Jumps to the function's exit.
    exits: Vec<usize>,
}

/// Does the integer fit the 64 bits compiled code works in?
fn word(n: i128) -> Option<i64> {
    i64::try_from(n).ok()
}

impl Asm {
    fn b(&mut self, bytes: &[u8]) {
        self.buf.extend_from_slice(bytes);
    }

    fn d32(&mut self, v: i32) {
        self.b(&v.to_le_bytes());
    }

    fn q(&mut self, v: u64) {
        self.b(&v.to_le_bytes());
    }

    /// The byte offset of a local's part.
    fn slot(i: usize, off: i32) -> i32 {
        (i as i32) * 32 + off
    }

    /// `mov rax, imm64`
    fn rax(&mut self, v: u64) {
        self.b(&[0x48, 0xB8]);
        self.q(v);
    }

    /// `mov rcx, imm64`
    fn rcx(&mut self, v: u64) {
        self.b(&[0x48, 0xB9]);
        self.q(v);
    }

    /// `mov rdx, imm64`
    fn rdx(&mut self, v: u64) {
        self.b(&[0x48, 0xBA]);
        self.q(v);
    }

    /// `mov rsi, imm64`
    fn rsi(&mut self, v: u64) {
        self.b(&[0x48, 0xBE]);
        self.q(v);
    }

    fn call(&mut self, f: usize) {
        self.rax(f as u64);
        self.b(&[0xFF, 0xD0]);
    }

    /// A conditional jump (the second opcode byte given) to be patched: where
    /// its offset is.
    fn jcc(&mut self, cc: u8) -> usize {
        self.b(&[0x0F, cc]);
        self.d32(0);
        self.buf.len() - 4
    }

    fn jmp(&mut self) -> usize {
        self.b(&[0xE9]);
        self.d32(0);
        self.buf.len() - 4
    }

    /// Make the jump whose offset is at `site` land here.
    fn land(&mut self, site: usize) {
        let rel = (self.buf.len() - (site + 4)) as i32;
        self.buf[site..site + 4].copy_from_slice(&rel.to_le_bytes());
    }

    /// `r11 = r13 + r12 * 32`: where the next local goes.
    fn next(&mut self) {
        self.b(&[0x4D, 0x89, 0xE3, 0x49, 0xC1, 0xE3, 0x05, 0x4D, 0x01, 0xEB]);
    }

    /// `inc r12`
    fn pushed(&mut self) {
        self.b(&[0x49, 0xFF, 0xC4]);
    }

    /// `cmp byte [r13 + slot], 0`, then a jump if it is not an integer.
    fn unless_int(&mut self, i: usize) -> usize {
        self.b(&[0x41, 0x80, 0xBD]);
        self.d32(Self::slot(i, 0));
        self.b(&[0x00]);
        self.jcc(0x85)
    }

    /// Copy the 32 bytes of local `i` to where `r11` points.
    fn copy(&mut self, i: usize) {
        self.b(&[0x41, 0x0F, 0x10, 0x85]);
        self.d32(Self::slot(i, 0));
        self.b(&[0x41, 0x0F, 0x10, 0x8D]);
        self.d32(Self::slot(i, 16));
        self.b(&[0x41, 0x0F, 0x11, 0x03]);
        self.b(&[0x41, 0x0F, 0x11, 0x4B, 0x10]);
    }

    /// Store `rax`, with its sign, as the next local, an integer.
    fn store_int(&mut self) {
        self.next();
        self.b(&[0x49, 0x89, 0x43, 0x10]); // mov [r11+16], rax
        self.b(&[0x48, 0x89, 0xC2, 0x48, 0xC1, 0xFA, 0x3F]); // mov rdx, rax; sar rdx, 63
        self.b(&[0x49, 0x89, 0x53, 0x18]); // mov [r11+24], rdx
        self.b(&[0x41, 0xC6, 0x03, 0x00]); // mov byte [r11], 0
        self.pushed();
    }

    /// An integer operand into `rax` (`first`) or `rcx`. The jumps to take if
    /// it is not an integer of 64 bits are added to `slow`. Nothing if the
    /// operand is written out and does not fit.
    fn operand(&mut self, a: &Atom, first: bool, slow: &mut Vec<usize>) -> Option<()> {
        match a {
            Atom::Int(n) => {
                let n = word(*n)? as u64;
                if first {
                    self.rax(n)
                } else {
                    self.rcx(n)
                }
            }
            Atom::Var(i) | Atom::Take(i) => {
                slow.push(self.unless_int(*i));
                // mov rax|rcx, [r13 + slot + 16]
                self.b(&[0x49, 0x8B, if first { 0x85 } else { 0x8D }]);
                self.d32(Self::slot(*i, 16));
                // mov rdx, [r13 + slot + 24]
                self.b(&[0x49, 0x8B, 0x95]);
                self.d32(Self::slot(*i, 24));
                // mov rsi, rax|rcx; sar rsi, 63; cmp rdx, rsi
                self.b(&[0x48, 0x89, if first { 0xC6 } else { 0xCE }]);
                self.b(&[0x48, 0xC1, 0xFE, 0x3F, 0x48, 0x39, 0xF2]);
                slow.push(self.jcc(0x85));
            }
        }
        Some(())
    }

    /// The instruction as the interpreter runs it.
    fn generic(&mut self, pc: usize, fail: Option<usize>) {
        self.b(&[0x48, 0x89, 0xDF]); // mov rdi, rbx
        self.rsi(pc as u64);
        self.b(&[0x4C, 0x89, 0xE2]); // mov rdx, r12
        self.call(glo_step as *const () as usize);
        self.b(&[0x49, 0x89, 0xD4]); // mov r12, rdx
        self.b(&[0x48, 0x83, 0xF8, 0x01]); // cmp rax, 1
        let out = self.jcc(0x84);
        self.exits.push(out);
        if let Some(fail) = fail {
            self.b(&[0x48, 0x83, 0xF8, 0x02]); // cmp rax, 2
            let site = self.jcc(0x84);
            self.jumps.push((site, fail));
        }
    }

    /// The code for one instruction. What has no code of its own is run as
    /// the interpreter runs it.
    fn instr(&mut self, pc: usize, instr: &Instr) {
        match instr {
            Instr::Op(Rhs::Atom(Atom::Int(n))) => {
                self.next();
                self.rax(*n as u64);
                self.b(&[0x49, 0x89, 0x43, 0x10]);
                self.rax((*n >> 64) as u64);
                self.b(&[0x49, 0x89, 0x43, 0x18]);
                self.b(&[0x41, 0xC6, 0x03, 0x00]);
                self.pushed();
            }
            Instr::Op(Rhs::Atom(Atom::Take(i))) => {
                self.next();
                self.copy(*i);
                // mov byte [r13 + slot], 0: what is left is an integer.
                self.b(&[0x41, 0xC6, 0x85]);
                self.d32(Self::slot(*i, 0));
                self.b(&[0x00]);
                self.pushed();
            }
            Instr::Op(Rhs::Atom(Atom::Var(i))) => {
                let other = self.unless_int(*i);
                self.next();
                self.copy(*i);
                let done = self.jmp();
                self.land(other);
                self.b(&[0x4C, 0x89, 0xEF]); // mov rdi, r13
                self.rsi(*i as u64);
                self.b(&[0x4C, 0x89, 0xE2]); // mov rdx, r12
                self.call(glo_copy as *const () as usize);
                self.land(done);
                self.pushed();
            }
            Instr::Op(Rhs::Prim(p @ (Prim::Add | Prim::Sub | Prim::Mul | Prim::Lt | Prim::Eq), args))
                if args.len() == 2 =>
            {
                let mut slow = Vec::new();
                let start = self.buf.len();
                let loaded = self
                    .operand(&args[0], true, &mut slow)
                    .and_then(|()| self.operand(&args[1], false, &mut slow));
                if loaded.is_none() {
                    self.buf.truncate(start);
                    return self.generic(pc, None);
                }
                match p {
                    Prim::Add => self.b(&[0x48, 0x01, 0xC8]),
                    Prim::Sub => self.b(&[0x48, 0x29, 0xC8]),
                    Prim::Mul => self.b(&[0x48, 0x0F, 0xAF, 0xC1]),
                    // cmp rax, rcx; setl|sete al; movzx eax, al
                    Prim::Lt => self.b(&[0x48, 0x39, 0xC8, 0x0F, 0x9C, 0xC0, 0x0F, 0xB6, 0xC0]),
                    _ => self.b(&[0x48, 0x39, 0xC8, 0x0F, 0x94, 0xC0, 0x0F, 0xB6, 0xC0]),
                }
                if matches!(p, Prim::Add | Prim::Sub | Prim::Mul) {
                    slow.push(self.jcc(0x80)); // jo
                }
                self.store_int();
                let done = self.jmp();
                for site in slow {
                    self.land(site);
                }
                self.generic(pc, None);
                self.land(done);
            }
            Instr::Op(Rhs::Place(Place { var, path })) if path.len() == 1 => {
                self.b(&[0x4C, 0x89, 0xEF]); // mov rdi, r13
                self.rsi(*var as u64);
                self.rdx(path[0] as u64);
                self.b(&[0x4C, 0x89, 0xE1]); // mov rcx, r12
                self.call(glo_field as *const () as usize);
                self.b(&[0x48, 0x85, 0xC0]); // test rax, rax
                let absent = self.jcc(0x84);
                self.pushed();
                let done = self.jmp();
                self.land(absent);
                self.generic(pc, None);
                self.land(done);
            }
            Instr::TestInt(Place { var, path }, n, fail) if path.is_empty() => {
                let site = self.unless_int(*var);
                self.jumps.push((site, *fail));
                for (off, part) in [(16, *n as u64), (24, (*n >> 64) as u64)] {
                    self.rax(part);
                    self.b(&[0x49, 0x39, 0x85]); // cmp [r13 + slot + off], rax
                    self.d32(Self::slot(*var, off));
                    let site = self.jcc(0x85);
                    self.jumps.push((site, *fail));
                }
            }
            Instr::TestCtor(Place { var, path }, tag, arity, fail) if path.is_empty() => {
                self.b(&[0x49, 0x8D, 0xBD]); // lea rdi, [r13 + slot]
                self.d32(Self::slot(*var, 0));
                self.rsi(*tag);
                self.rdx(*arity as u64);
                self.call(glo_is_ctor as *const () as usize);
                self.b(&[0x48, 0x85, 0xC0]);
                let site = self.jcc(0x84);
                self.jumps.push((site, *fail));
            }
            Instr::Jump(t) => {
                let site = self.jmp();
                self.jumps.push((site, *t));
            }
            other => self.generic(pc, other.fail()),
        }
    }

    /// A function: where it starts, and where its table of instruction
    /// addresses is, which is filled in once the code has an address.
    fn function(&mut self, code: &[Instr]) -> (usize, usize) {
        let entry = self.buf.len();
        self.at.clear();
        self.jumps.clear();
        self.exits.clear();
        // push rbx; push r12; push r13: the stack is then aligned for calls.
        self.b(&[0x53, 0x41, 0x54, 0x41, 0x55]);
        // mov rbx, rdi; mov r13, rsi; mov r12, rcx
        self.b(&[0x48, 0x89, 0xFB, 0x49, 0x89, 0xF5, 0x49, 0x89, 0xCC]);
        // lea rax, [rip + table]; jmp [rax + rdx*8]
        self.b(&[0x48, 0x8D, 0x05]);
        self.d32(0);
        let table_ref = self.buf.len() - 4;
        self.b(&[0xFF, 0x24, 0xD0]);
        for (pc, instr) in code.iter().enumerate() {
            self.at.push(self.buf.len());
            self.instr(pc, instr);
        }
        // Past the last instruction, where a test that fails in the last
        // clause goes: the interpreter says what that is.
        self.at.push(self.buf.len());
        self.generic(code.len(), None);
        // Every way out: pop and return.
        let exit = self.buf.len();
        self.b(&[0x41, 0x5D, 0x41, 0x5C, 0x5B, 0xC3]);
        for (site, pc) in std::mem::take(&mut self.jumps) {
            let target = self.at.get(pc).copied().unwrap_or(exit);
            let rel = target as i64 - (site as i64 + 4);
            self.buf[site..site + 4].copy_from_slice(&(rel as i32).to_le_bytes());
        }
        for site in std::mem::take(&mut self.exits) {
            let rel = exit as i64 - (site as i64 + 4);
            self.buf[site..site + 4].copy_from_slice(&(rel as i32).to_le_bytes());
        }
        while self.buf.len() % 8 != 0 {
            self.b(&[0x90]);
        }
        let table = self.buf.len();
        let rel = table as i64 - (table_ref as i64 + 4);
        self.buf[table_ref..table_ref + 4].copy_from_slice(&(rel as i32).to_le_bytes());
        for i in 0..code.len() {
            let at = self.at[i] as u64;
            self.q(at);
        }
        (entry, table)
    }
}

/// Compile the functions `pick` chooses. The code is never freed: it lasts as
/// long as the program runs.
pub fn compile(codes: &[Vec<Instr>], pick: impl Fn(usize) -> bool) -> Vec<Option<Body>> {
    let mut asm = Asm::default();
    let mut placed: Vec<Option<(usize, usize, usize)>> = Vec::new();
    for (f, code) in codes.iter().enumerate() {
        if pick(f) && !code.is_empty() {
            let (entry, table) = asm.function(code);
            placed.push(Some((entry, table, code.len())));
        } else {
            placed.push(None);
        }
    }
    if asm.buf.is_empty() {
        return vec![None; codes.len()];
    }
    // Readable, writable and executable, private, backed by nothing.
    let size = asm.buf.len().next_multiple_of(4096);
    let base = unsafe { mmap(std::ptr::null_mut(), size, 7, 0x22, -1, 0) };
    if base as isize == -1 {
        eprintln!("no memory for compiled code: the program is interpreted");
        return vec![None; codes.len()];
    }
    // The tables hold addresses, which are known only now.
    for (_, table, count) in placed.iter().flatten() {
        for i in 0..*count {
            let at = table + i * 8;
            let rel = u64::from_le_bytes(asm.buf[at..at + 8].try_into().unwrap());
            asm.buf[at..at + 8].copy_from_slice(&(base as u64 + rel).to_le_bytes());
        }
    }
    unsafe { std::ptr::copy_nonoverlapping(asm.buf.as_ptr(), base, asm.buf.len()) };
    placed
        .iter()
        .map(|p| {
            p.map(|(entry, _, _)| unsafe { std::mem::transmute::<*mut u8, Body>(base.add(entry)) })
        })
        .collect()
}
