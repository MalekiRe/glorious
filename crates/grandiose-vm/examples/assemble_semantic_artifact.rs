//! Receiving-IR bridge for the Lean compiler. This program never reads source,
//! resolves a source name, selects an implementation, or invokes Stage0.
//! The Lean producer supplies the complete VM instruction/type/interface tables.
//! This bridge handles the existing wire codec, canonical cleanup metadata and
//! independent receiving verification, including verification after decoding.

use grandiose_vm::bytecode::{
    Artifact, CleanupPlan, Constant, DropGlue, Export, Function, HandlerDef, Import, Instruction,
    Protocol, ReferenceReturnContract, Type,
};
use grandiose_vm::verify::{verify, with_generated_cleanup_plans};
use serde::Deserialize;
use serde_json::value::RawValue;
use std::error::Error;
use std::io::{Read, Write};
use std::path::Path;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    target_pointer_bits: u32,
    target_layout_identity: String,
    target_little_endian: bool,
    required_features: u64,
    entry_function: Option<u32>,
    types: Vec<Type>,
    constants: Vec<Box<RawValue>>,
    imports: Vec<Import>,
    protocols: Vec<Protocol>,
    handler_defs: Vec<HandlerDef>,
    cleanups: Vec<CleanupPlan>,
    exports: Vec<Export>,
    drop_glue: Vec<DropGlue>,
    reference_return_contracts: Vec<ReferenceReturnContract>,
    functions: Vec<Function>,
    code: Vec<Instruction>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct FloatBits {
    float_width: u32,
    float_bits: u64,
}

fn constant(value: Box<RawValue>) -> Result<Constant, Box<dyn Error>> {
    if let Ok(float) = serde_json::from_str::<FloatBits>(value.get()) {
        return match float.float_width {
            32 => Ok(Constant::F32(f32::from_bits(u32::try_from(
                float.float_bits,
            )?))),
            64 => Ok(Constant::F64(f64::from_bits(float.float_bits))),
            _ => Err("unsupported IEEE format in semantic artifact".into()),
        };
    }
    // Deserialize integers directly, preserving the complete i128/u128 range.
    // Passing through serde_json::Value or an f64 would lose this information.
    Ok(serde_json::from_str(value.get())?)
}

fn assemble(input: Input) -> Result<Vec<u8>, Box<dyn Error>> {
    if input.target_pointer_bits != 64
        || input.target_layout_identity != "grandiose-vm64-v1"
        || !input.target_little_endian
    {
        return Err("the selected target layout is not supported by this VM64 codec bridge".into());
    }
    let mut artifact = Artifact {
        required_features: input.required_features,
        entry_function: input.entry_function,
        types: input.types,
        constants: input
            .constants
            .into_iter()
            .map(constant)
            .collect::<Result<_, _>>()?,
        imports: input.imports,
        protocols: input.protocols,
        handler_defs: input.handler_defs,
        cleanups: input.cleanups,
        exports: input.exports,
        drop_glue: input.drop_glue,
        reference_return_contracts: input.reference_return_contracts,
        functions: input.functions,
        code: input.code,
    };
    artifact.canonicalize_constants();
    // Cleanup tables are canonical metadata for these already-selected VM
    // instructions, not a second source destruction decision or a permission
    // to discard an exact owner. The independent verifier checks that boundary.
    artifact = with_generated_cleanup_plans(artifact)?;
    verify(artifact.clone())?;
    let bytes = artifact.encode();
    let decoded = Artifact::decode(&bytes)?;
    verify(decoded)?;
    Ok(bytes)
}

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = std::env::args().skip(1);
    if arguments.next().as_deref() != Some("--output") {
        return Err("usage: assemble_semantic_artifact --output FILE.grbc < artifact.json".into());
    }
    let destination = arguments.next().ok_or("missing output path")?;
    if arguments.next().is_some() {
        return Err("unexpected argument".into());
    }
    let mut text = String::new();
    std::io::stdin().read_to_string(&mut text)?;
    let bytes = assemble(serde_json::from_str(&text)?)?;
    let path = Path::new(&destination);
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let mut temporary = tempfile::NamedTempFile::new_in(parent)?;
    temporary.write_all(&bytes)?;
    temporary.flush()?;
    temporary.persist(path)?;
    eprintln!("wrote independently verified semantic artifact: {destination}");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("semantic-artifact: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw(text: &str) -> Box<RawValue> {
        RawValue::from_string(text.to_owned()).unwrap()
    }

    #[test]
    fn constants_preserve_integer_width_and_ieee_bits() {
        assert_eq!(
            constant(raw(r#"{"U128":340282366920938463463374607431768211455}"#)).unwrap(),
            Constant::U128(u128::MAX)
        );
        assert_eq!(
            constant(raw(r#"{"I128":-170141183460469231731687303715884105728}"#)).unwrap(),
            Constant::I128(i128::MIN)
        );
        let Constant::F32(value) =
            constant(raw(r#"{"float_width":32,"float_bits":2147483648}"#)).unwrap()
        else {
            panic!("wrong scalar format")
        };
        assert_eq!(value.to_bits(), (-0.0_f32).to_bits());
        let Constant::F64(value) = constant(raw(
            r#"{"float_width":64,"float_bits":9221120237041090560}"#,
        ))
        .unwrap() else {
            panic!("wrong scalar format")
        };
        assert_eq!(value.to_bits(), 0x7ff8_0000_0000_0000);
        assert!(constant(raw(r#"{"float_width":32,"float_bits":4294967296}"#)).is_err());
        assert!(constant(raw(r#"{"float_width":16,"float_bits":0}"#)).is_err());
    }

    fn minimal_input() -> Input {
        Input {
            target_pointer_bits: 64,
            target_layout_identity: "grandiose-vm64-v1".into(),
            target_little_endian: true,
            required_features: 1,
            entry_function: Some(0),
            types: Type::predefined(),
            constants: vec![raw(r#""Unit""#)],
            imports: vec![],
            protocols: vec![],
            handler_defs: vec![],
            cleanups: vec![],
            exports: vec![],
            drop_glue: vec![],
            reference_return_contracts: vec![],
            functions: vec![Function {
                name: "entry".into(),
                flags: 0,
                params: vec![],
                return_type: 0,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![0, 0],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            }],
            code: vec![
                Instruction::Const {
                    dst: 1,
                    constant: 0,
                },
                Instruction::Return { src: Some(1) },
            ],
        }
    }

    #[test]
    fn receiving_boundary_checks_fresh_and_decoded_tables() {
        let bytes = assemble(minimal_input()).unwrap();
        verify(Artifact::decode(&bytes).unwrap()).unwrap();
        let mut mismatched = minimal_input();
        mismatched.target_pointer_bits = 32;
        assert!(assemble(mismatched).is_err());
        let mut invalid = minimal_input();
        invalid.code[1] = Instruction::Return { src: Some(20) };
        assert!(assemble(invalid).is_err());
    }
}
