//! The LLVM backend: a module of LLVM IR for a program, to be compiled and
//! linked with this library into a program of its own.
//!
//! It makes the code the x86-64 backend makes, instruction for instruction,
//! and leaves it to LLVM to make it good. The module carries the program's
//! bytecode, so that what it has no code for can still be interpreted, and a
//! `main` that hands both to the runtime. The contract is `docs/abi.md`.

use super::*;
use std::fmt::Write as _;

struct Emit {
    out: String,
    /// How many names this function has used.
    fresh: usize,
}

impl Emit {
    fn name(&mut self) -> String {
        self.fresh += 1;
        format!("%t{}", self.fresh)
    }

    fn line(&mut self, text: &str) {
        self.out.push_str("  ");
        self.out.push_str(text);
        self.out.push('\n');
    }

    fn label(&mut self, name: &str) {
        let _ = writeln!(self.out, "{name}:");
    }

    /// How many locals there are.
    fn len(&mut self) -> String {
        let l = self.name();
        self.line(&format!("{l} = load i64, ptr %len"));
        l
    }

    /// Where local `i` is.
    fn local(&mut self, i: usize) -> String {
        let p = self.name();
        self.line(&format!("{p} = getelementptr %V, ptr %locals, i64 {i}"));
        p
    }

    /// Where the next local goes, and how many there are.
    fn next(&mut self) -> (String, String) {
        let l = self.len();
        let p = self.name();
        self.line(&format!("{p} = getelementptr %V, ptr %locals, i64 {l}"));
        (p, l)
    }

    /// One more local than `l`.
    fn pushed(&mut self, l: &str) {
        let n = self.name();
        self.line(&format!("{n} = add i64 {l}, 1"));
        self.line(&format!("store i64 {n}, ptr %len"));
    }

    /// An integer as the next local.
    fn store_int(&mut self, wide: &str) {
        let (d, l) = self.next();
        let p = self.name();
        self.line(&format!("store i8 0, ptr {d}"));
        self.line(&format!("{p} = getelementptr i8, ptr {d}, i64 16"));
        self.line(&format!("store i128 {wide}, ptr {p}, align 16"));
        self.pushed(&l);
    }

    /// The integer a local holds, in 128 bits; control goes to `other` if it
    /// holds something else.
    fn wide(&mut self, i: usize, other: &str) -> String {
        let s = self.local(i);
        let (tag, is, p, v) = (self.name(), self.name(), self.name(), self.name());
        let here = self.name().replace('%', "b");
        self.line(&format!("{tag} = load i8, ptr {s}"));
        self.line(&format!("{is} = icmp eq i8 {tag}, 0"));
        self.line(&format!("br i1 {is}, label %{here}, label %{other}"));
        self.label(&here);
        self.line(&format!("{p} = getelementptr i8, ptr {s}, i64 16"));
        self.line(&format!("{v} = load i128, ptr {p}, align 16"));
        v
    }

    /// An integer operand in 64 bits; control goes to `slow` if it is not
    /// one. Nothing if it is written out and does not fit.
    fn operand(&mut self, a: &Atom, slow: &str) -> Option<String> {
        match a {
            Atom::Int(n) => i64::try_from(*n).ok().map(|n| n.to_string()),
            Atom::Var(i) | Atom::Take(i) => {
                let v = self.wide(*i, slow);
                let (lo, back, fits) = (self.name(), self.name(), self.name());
                let here = self.name().replace('%', "b");
                self.line(&format!("{lo} = trunc i128 {v} to i64"));
                self.line(&format!("{back} = sext i64 {lo} to i128"));
                self.line(&format!("{fits} = icmp eq i128 {back}, {v}"));
                self.line(&format!("br i1 {fits}, label %{here}, label %{slow}"));
                self.label(&here);
                Some(lo)
            }
        }
    }

    /// The instruction as the interpreter runs it.
    fn generic(&mut self, pc: usize, next: &str, fail: Option<usize>) {
        let l = self.len();
        let (r, st, nl) = (self.name(), self.name(), self.name());
        self.line(&format!("{r} = call %StepOut @glo_step(ptr %vm, i64 {pc}, i64 {l})"));
        self.line(&format!("{st} = extractvalue %StepOut {r}, 0"));
        self.line(&format!("{nl} = extractvalue %StepOut {r}, 1"));
        self.line(&format!("store i64 {nl}, ptr %len"));
        let failed = match fail {
            Some(f) => format!(" i64 2, label %pc{f}"),
            None => String::new(),
        };
        self.line(&format!("switch i64 {st}, label %exit [ i64 0, label %{next}{failed} ]"));
    }

    /// After a call that did the instruction if it was simple, and said so:
    /// one more local, or the instruction as the interpreter runs it.
    fn simple_or_generic(&mut self, pc: usize, next: &str, done: &str, l: &str) {
        let was = self.name();
        let (simple, not) = (format!("p{pc}"), format!("s{pc}"));
        self.line(&format!("{was} = icmp ne i64 {done}, 0"));
        self.line(&format!("br i1 {was}, label %{simple}, label %{not}"));
        self.label(&simple);
        self.pushed(l);
        self.line(&format!("br label %{next}"));
        self.label(&not);
        self.generic(pc, next, None);
    }

    fn instr(&mut self, pc: usize, instr: &Instr, next: &str) {
        match instr {
            Instr::Op(Rhs::Atom(Atom::Int(n))) => {
                self.store_int(&n.to_string());
                self.line(&format!("br label %{next}"));
            }
            Instr::Op(Rhs::Atom(Atom::Take(i))) => {
                let s = self.local(*i);
                let (d, l) = self.next();
                self.line(&format!(
                    "call void @llvm.memcpy.p0.p0.i64(ptr align 16 {d}, ptr align 16 {s}, i64 32, i1 false)"
                ));
                self.line(&format!("store i8 0, ptr {s}"));
                self.pushed(&l);
                self.line(&format!("br label %{next}"));
            }
            Instr::Op(Rhs::Atom(Atom::Var(i))) => {
                let s = self.local(*i);
                let (d, l) = self.next();
                let (tag, is) = (self.name(), self.name());
                let (plain, other, done) = (format!("p{pc}"), format!("o{pc}"), format!("d{pc}"));
                self.line(&format!("{tag} = load i8, ptr {s}"));
                self.line(&format!("{is} = icmp eq i8 {tag}, 0"));
                self.line(&format!("br i1 {is}, label %{plain}, label %{other}"));
                self.label(&plain);
                self.line(&format!(
                    "call void @llvm.memcpy.p0.p0.i64(ptr align 16 {d}, ptr align 16 {s}, i64 32, i1 false)"
                ));
                self.line(&format!("br label %{done}"));
                self.label(&other);
                self.line(&format!("call void @glo_copy(ptr %locals, i64 {i}, i64 {l})"));
                self.line(&format!("br label %{done}"));
                self.label(&done);
                self.pushed(&l);
                self.line(&format!("br label %{next}"));
            }
            Instr::Op(Rhs::Prim(p @ (Prim::Add | Prim::Sub | Prim::Mul | Prim::Lt | Prim::Eq), args))
                if args.len() == 2
                    && args.iter().all(|a| !matches!(a, Atom::Int(n) if i64::try_from(*n).is_err())) =>
            {
                let slow = format!("s{pc}");
                let a = self.operand(&args[0], &slow).unwrap();
                let b = self.operand(&args[1], &slow).unwrap();
                let wide = self.name();
                match p {
                    Prim::Add | Prim::Sub | Prim::Mul => {
                        let op = match p {
                            Prim::Add => "sadd",
                            Prim::Sub => "ssub",
                            _ => "smul",
                        };
                        let (r, v, over) = (self.name(), self.name(), self.name());
                        let fits = format!("f{pc}");
                        self.line(&format!(
                            "{r} = call {{ i64, i1 }} @llvm.{op}.with.overflow.i64(i64 {a}, i64 {b})"
                        ));
                        self.line(&format!("{v} = extractvalue {{ i64, i1 }} {r}, 0"));
                        self.line(&format!("{over} = extractvalue {{ i64, i1 }} {r}, 1"));
                        self.line(&format!("br i1 {over}, label %{slow}, label %{fits}"));
                        self.label(&fits);
                        self.line(&format!("{wide} = sext i64 {v} to i128"));
                    }
                    _ => {
                        let c = self.name();
                        let how = if matches!(p, Prim::Lt) { "slt" } else { "eq" };
                        self.line(&format!("{c} = icmp {how} i64 {a}, {b}"));
                        self.line(&format!("{wide} = zext i1 {c} to i128"));
                    }
                }
                self.store_int(&wide);
                self.line(&format!("br label %{next}"));
                self.label(&slow);
                self.generic(pc, next, None);
            }
            Instr::Op(Rhs::Place(Place { var, path })) if path.len() == 1 => {
                let l = self.len();
                let (r, found) = (self.name(), self.name());
                let (there, absent) = (format!("p{pc}"), format!("s{pc}"));
                self.line(&format!(
                    "{r} = call i64 @glo_field(ptr %locals, i64 {var}, i64 {}, i64 {l})",
                    path[0]
                ));
                self.line(&format!("{found} = icmp ne i64 {r}, 0"));
                self.line(&format!("br i1 {found}, label %{there}, label %{absent}"));
                self.label(&there);
                self.pushed(&l);
                self.line(&format!("br label %{next}"));
                self.label(&absent);
                self.generic(pc, next, None);
            }
            Instr::TestInt(Place { var, path }, n, fail) if path.is_empty() => {
                let v = self.wide(*var, &format!("pc{fail}"));
                let same = self.name();
                self.line(&format!("{same} = icmp eq i128 {v}, {n}"));
                self.line(&format!("br i1 {same}, label %{next}, label %pc{fail}"));
            }
            Instr::TestCtor(Place { var, path }, tag, arity, fail) if path.is_empty() => {
                let s = self.local(*var);
                let (r, is) = (self.name(), self.name());
                self.line(&format!("{r} = call i64 @glo_is_ctor(ptr {s}, i64 {tag}, i64 {arity})"));
                self.line(&format!("{is} = icmp ne i64 {r}, 0"));
                self.line(&format!("br i1 {is}, label %{next}, label %pc{fail}"));
            }
            Instr::Jump(t) => self.line(&format!("br label %pc{t}")),
            Instr::Again(to, keep) => {
                let l = self.len();
                self.line(&format!("call void @glo_again(ptr %vm, i64 {l}, i64 {keep})"));
                self.line(&format!("store i64 {keep}, ptr %len"));
                self.line(&format!("br label %pc{to}"));
            }
            Instr::Mem(MemOp::Load, args) if matches!(args.as_slice(), [Atom::Var(_) | Atom::Take(_)]) => {
                let (Atom::Var(r) | Atom::Take(r)) = args[0] else { unreachable!() };
                let l = self.len();
                let done = self.name();
                self.line(&format!("{done} = call i64 @glo_load(ptr %vm, ptr %locals, i64 {r}, i64 {l})"));
                self.simple_or_generic(pc, next, &done, &l);
            }
            Instr::Mem(MemOp::Store, args)
                if matches!(args.as_slice(), [Atom::Var(_) | Atom::Take(_), Atom::Var(_) | Atom::Take(_)]) =>
            {
                let (Atom::Var(r) | Atom::Take(r)) = args[0] else { unreachable!() };
                let (v, take) = match args[1] {
                    Atom::Take(v) => (v, 1),
                    Atom::Var(v) => (v, 0),
                    Atom::Int(_) => unreachable!(),
                };
                let l = self.len();
                let done = self.name();
                self.line(&format!(
                    "{done} = call i64 @glo_store(ptr %vm, ptr %locals, i64 {r}, i64 {v}, i64 {take}, i64 {l})"
                ));
                self.simple_or_generic(pc, next, &done, &l);
            }
            other => self.generic(pc, next, other.fail()),
        }
    }

    fn function(&mut self, f: usize, code: &[Instr]) {
        self.fresh = 0;
        let _ = writeln!(
            self.out,
            "define i64 @glo_f{f}(ptr %vm, ptr %locals, i64 %pc, i64 %len0) {{\nentry:"
        );
        self.line("%len = alloca i64");
        self.line("store i64 %len0, ptr %len");
        let cases: String = (0..code.len()).map(|pc| format!(" i64 {pc}, label %pc{pc}")).collect();
        self.line(&format!("switch i64 %pc, label %exit [{cases} ]"));
        for (pc, instr) in code.iter().enumerate() {
            self.label(&format!("pc{pc}"));
            self.instr(pc, instr, &format!("pc{}", pc + 1));
        }
        // Past the last instruction, where a test that fails in the last
        // clause goes: the interpreter says what that is.
        self.label(&format!("pc{}", code.len()));
        self.generic(code.len(), "exit", None);
        self.label("exit");
        self.line("ret i64 0");
        self.out.push_str("}\n\n");
    }
}

/// The module for a program: a body for every function, the bytecode, and a
/// `main`.
pub fn emit(program: &Program, bytes: &[u8], rewritten: bool) -> String {
    let mut e = Emit { out: String::new(), fresh: 0 };
    e.out.push_str(
        "; Glorious, compiled. Link with libglorious_vm.a.\n\
         target triple = \"x86_64-unknown-linux-gnu\"\n\n\
         %V = type { i8, [15 x i8], i64, i64 }\n\
         %StepOut = type { i64, i64 }\n\n\
         declare %StepOut @glo_step(ptr, i64, i64)\n\
         declare void @glo_copy(ptr, i64, i64)\n\
         declare i64 @glo_is_ctor(ptr, i64, i64)\n\
         declare i64 @glo_field(ptr, i64, i64, i64)\n\
         declare void @glo_again(ptr, i64, i64)\n\
         declare i64 @glo_load(ptr, ptr, i64, i64)\n\
         declare i64 @glo_store(ptr, ptr, i64, i64, i64, i64)\n\
         declare i32 @glo_main(i64, i64, ptr, i64, ptr, i64, i32, ptr)\n\
         declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)\n\
         declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)\n\
         declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)\n\
         declare { i64, i1 } @llvm.smul.with.overflow.i64(i64, i64)\n\n",
    );
    for (f, code) in program.codes.iter().enumerate() {
        e.function(f, code);
    }
    let escaped: String = bytes.iter().map(|b| format!("\\{b:02X}")).collect();
    let count = program.codes.len();
    let bodies: Vec<String> = (0..count).map(|f| format!("ptr @glo_f{f}")).collect();
    let _ = write!(
        e.out,
        "@glo_bytes = private constant [{n} x i8] c\"{escaped}\"\n\
         @glo_bodies = private constant [{count} x ptr] [{bodies}]\n\n\
         define i32 @main(i32 %argc, ptr %argv) {{\n  \
         %r = call i32 @glo_main(i64 {abi}, i64 {rewritten}, ptr @glo_bytes, i64 {n}, ptr @glo_bodies, i64 {count}, i32 %argc, ptr %argv)\n  \
         ret i32 %r\n}}\n",
        n = bytes.len(),
        abi = native::ABI,
        rewritten = u64::from(rewritten),
        bodies = bodies.join(", "),
    );
    e.out
}
