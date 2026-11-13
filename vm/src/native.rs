//! Running compiled code, and what compiled code asks of the runtime.
//!
//! The contract is `docs/abi.md`. A function's compiled body runs the
//! function from an instruction of it until control leaves the activation: a
//! call, a return, an effect. The activation's locals stay where the
//! interpreter keeps them, so a function that is interpreted and one that is
//! compiled call each other, capture each other in resumptions and unwind
//! through each other without knowing which the other is.

use super::*;

/// The generation of the contract between compiled code and this runtime.
/// Code built for another is refused before any of it runs.
pub const ABI: u64 = 2;

/// A function's compiled body: the machine, the activation's locals, the
/// instruction to start from, and how many locals there are. It returns 0
/// when control has left the activation or the machine has stopped, and 1,
/// having done nothing, if it cannot start from that instruction.
pub type Body = unsafe extern "C" fn(vm: *mut Vm, locals: *mut Value, pc: u64, len: u64) -> u64;

/// What a step did: whether compiled code goes on, and with how many locals.
#[repr(C)]
pub struct StepOut {
    /// 0: the next instruction. 2: the instruction a failed test names.
    /// 1: control has left the activation, or the machine has stopped.
    status: u64,
    len: u64,
}

impl Vm {
    /// Run to the end. A function with a compiled body runs it; any other is
    /// interpreted.
    pub(crate) fn run(&mut self, bodies: &[Option<Body>]) -> Stop {
        loop {
            // (An instruction that is not there is the interpreter's to refuse.)
            let body = bodies.get(self.code).copied().flatten();
            match body.filter(|_| self.pc < self.codes[self.code].len()) {
                None => {
                    if let Err(stop) = self.step() {
                        return stop;
                    }
                }
                Some(body) => {
                    // The body keeps a pointer to the locals: they must not
                    // move while it pushes one for each instruction.
                    self.locals.reserve(self.codes[self.code].len() + 1);
                    let (pc, len) = (self.pc as u64, self.locals.len() as u64);
                    let entered = unsafe { body(self, self.locals.as_mut_ptr(), pc, len) };
                    if let Some(stop) = self.stop.take() {
                        return stop;
                    }
                    // A body need not start from every instruction: where
                    // it does not, the interpreter runs that one.
                    if entered != 0 {
                        if let Err(stop) = self.step() {
                            return stop;
                        }
                    }
                }
            }
        }
    }
}

/// Run the instruction at `pc` as the interpreter does. Compiled code calls
/// this for whatever it has no code of its own for, and for everything that
/// leaves the activation.
///
/// # Safety
/// `vm` is the machine the body was given, and `len` locals are initialised.
#[no_mangle]
pub unsafe extern "C" fn glo_step(vm: *mut Vm, pc: u64, len: u64) -> StepOut {
    let vm = &mut *vm;
    vm.locals.set_len(len as usize);
    let (code, base) = (vm.code, vm.locals.as_ptr());
    vm.pc = pc as usize;
    let fail = vm.codes[code].get(vm.pc).and_then(Instr::fail);
    match vm.step() {
        Err(stop) => {
            vm.stop = Some(stop);
            StepOut { status: 1, len: 0 }
        }
        Ok(()) => {
            // The same activation has the same locals in the same place: a
            // call, a return or an effect leaves it with others.
            let same = vm.code == code && vm.locals.as_ptr() == base;
            let len = vm.locals.len() as u64;
            if same && vm.pc as u64 == pc + 1 {
                StepOut { status: 0, len }
            } else if same && Some(vm.pc) == fail {
                StepOut { status: 2, len }
            } else {
                StepOut { status: 1, len }
            }
        }
    }
}

/// A copy of a local that is not an integer, as the next local.
///
/// # Safety
/// `locals` has `len` initialised values and room for one more; `i < len`.
#[no_mangle]
pub unsafe extern "C" fn glo_copy(locals: *mut Value, i: u64, len: u64) {
    let v = (*locals.add(i as usize)).clone();
    std::ptr::write(locals.add(len as usize), v);
}

/// Whether a value was built by constructor `tag` with `arity` fields.
///
/// # Safety
/// `v` points to an initialised value.
#[no_mangle]
pub unsafe extern "C" fn glo_is_ctor(v: *const Value, tag: u64, arity: u64) -> u64 {
    match &*v {
        Value::Data(d) => (d.tag == tag && d.fields.len() as u64 == arity) as u64,
        _ => 0,
    }
}

/// A field of a local, by a path of one step, as the next local.
/// Gives 0 if it is not there.
///
/// # Safety
/// As `glo_copy`.
#[no_mangle]
pub unsafe extern "C" fn glo_field(locals: *mut Value, i: u64, field: u64, len: u64) -> u64 {
    match &*locals.add(i as usize) {
        Value::Data(d) => match d.fields.get(field as usize) {
            Some(v) => {
                std::ptr::write(locals.add(len as usize), v.clone());
                1
            }
            None => 0,
        },
        _ => 0,
    }
}

/// Let go of the locals from `keep` on.
///
/// # Safety
/// As `glo_step`.
#[no_mangle]
pub unsafe extern "C" fn glo_again(vm: *mut Vm, len: u64, keep: u64) {
    let vm = &mut *vm;
    vm.locals.set_len(len as usize);
    vm.locals.truncate(keep as usize);
}

/// What the cell local `r` refers to holds, as the next local. Gives 0 if
/// it is not as simple as that: the reference is to a part, or the cell is
/// not there.
///
/// # Safety
/// As `glo_copy`, and `vm` is the machine.
#[no_mangle]
pub unsafe extern "C" fn glo_load(vm: *mut Vm, locals: *mut Value, r: u64, len: u64) -> u64 {
    let vm = &mut *vm;
    match &*locals.add(r as usize) {
        Value::Ref(addr, None) => match vm.cells.get(*addr) {
            Some(Some(v)) => {
                std::ptr::write(locals.add(len as usize), v.clone());
                1
            }
            _ => 0,
        },
        _ => 0,
    }
}

/// Put local `v` in the cell local `r` refers to, moving it if `take`; the
/// next local is the value with no parts. Gives 0 if it is not as simple
/// as that.
///
/// # Safety
/// As `glo_load`.
#[no_mangle]
pub unsafe extern "C" fn glo_store(vm: *mut Vm, locals: *mut Value, r: u64, v: u64, take: u64, len: u64) -> u64 {
    let vm = &mut *vm;
    let Value::Ref(addr, None) = &*locals.add(r as usize) else { return 0 };
    match vm.cells.get_mut(*addr) {
        Some(cell @ Some(_)) => {
            let from = locals.add(v as usize);
            let value = if take != 0 { std::mem::replace(&mut *from, Value::Int(0)) } else { (*from).clone() };
            *cell = Some(value);
            std::ptr::write(locals.add(len as usize), unit());
            1
        }
        _ => 0,
    }
}

/// The instructions a body may be asked to start from: the first, and each
/// that follows one control can leave the activation at and come back to.
pub fn starts_at(code: &[Instr]) -> Vec<bool> {
    (0..code.len())
        .map(|pc| {
            pc == 0
                || !matches!(
                    code[pc - 1],
                    Instr::Op(_)
                        | Instr::TestCtor(..)
                        | Instr::TestInt(..)
                        | Instr::Mem(..)
                        | Instr::Jump(_)
                        | Instr::Again(..)
                        | Instr::Enter { .. }
                        | Instr::Leave
                        | Instr::Stuck
                )
        })
        .collect()
}

/// A program built ahead of time: its bytecode, and the compiled body of
/// each function that has one. This is what the `main` of such a program
/// calls.
///
/// # Safety
/// `bytes` and `bodies` are what the program was built with; `argv` is the
/// process's.
#[no_mangle]
pub unsafe extern "C" fn glo_main(
    abi: u64,
    rewritten: u64,
    bytes: *const u8,
    size: u64,
    bodies: *const Option<Body>,
    count: u64,
    argc: i32,
    argv: *const *const std::ffi::c_char,
) -> i32 {
    if abi != ABI {
        eprintln!("this program was built for ABI generation {abi}, and this runtime is generation {ABI}");
        return 1;
    }
    let bytes = std::slice::from_raw_parts(bytes, size as usize);
    // The bodies were made from the bytecode as it was rewritten or as it
    // was written: it is read here the same way, whatever is said now.
    let program = match decode(bytes, rewritten != 0) {
        Ok(program) => program,
        Err(e) => {
            eprintln!("{e}");
            return 1;
        }
    };
    let args: Vec<String> = (1..argc as usize)
        .map(|i| std::ffi::CStr::from_ptr(*argv.add(i)).to_string_lossy().into_owned())
        .collect();
    let input = match inputs(&args) {
        Ok(input) => input,
        Err(e) => {
            eprintln!("{e}");
            return 64;
        }
    };
    let built = std::slice::from_raw_parts(bodies, count as usize);
    // Which functions run their built bodies is the builder's choice, and
    // can be narrowed when the program is run: `interp` runs none of them,
    // `x86` compiles every function again here, `mix` takes a third of the
    // functions from each of the three.
    let bodies: Vec<Option<Body>> = match std::env::var("GLORIOUS_BACKEND").as_deref() {
        Ok("interp") => Vec::new(),
        Ok("x86") => x86::compile(&program.codes, |_| true),
        Ok("mix") => {
            let jit = x86::compile(&program.codes, |f| f % 3 == 2);
            (0..program.codes.len())
                .map(|f| match f % 3 {
                    0 => built.get(f).copied().flatten(),
                    2 => jit[f],
                    _ => None,
                })
                .collect()
        }
        _ => built.to_vec(),
    };
    let mut vm = machine(program, input);
    i32::from(finish(&mut vm, &bodies))
}
