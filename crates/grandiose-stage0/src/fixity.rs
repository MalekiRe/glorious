//! Source-defined operator fixities and deterministic body grouping inputs.
//!
//! Bodies deliberately retain flat operator chains.  This table is built from
//! their owning module interface after all declaration headers are available;
//! no parser heuristic is permitted to choose associativity or precedence.

use std::collections::BTreeMap;

use crate::{
    header::{FixityForm, ParsedHeader},
    identity::{DefKey, Digest},
    interface::PackageInterface,
};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FixityPosition {
    Prefix,
    Infix,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fixity {
    pub declaration: Option<DefKey>,
    pub form: FixityForm,
    pub precedence: u8,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixityTable {
    entries: BTreeMap<(FixityPosition, String), Fixity>,
    fingerprint: Digest,
}

impl FixityTable {
    /// The stage-zero target has no separately compiled prelude yet.  These
    /// declarations mirror the language prelude so isolated package requests
    /// retain the same operator semantics.  Source declarations in the module
    /// replace an entry in their own position namespace.
    pub fn with_prelude() -> Self {
        let mut entries = BTreeMap::new();
        for (operator, precedence) in [
            ("+", 30),
            ("-", 30),
            ("*", 40),
            ("/", 40),
            ("%", 40),
            ("==", 20),
            ("!=", 20),
            ("<", 20),
            ("<=", 20),
            (">", 20),
            (">=", 20),
            ("or", 2),
            ("and", 3),
        ] {
            entries.insert(
                (FixityPosition::Infix, operator.into()),
                Fixity {
                    declaration: None,
                    form: FixityForm::InfixLeft,
                    precedence,
                },
            );
        }
        for (operator, precedence) in [("+", 50), ("-", 50), ("!", 50)] {
            entries.insert(
                (FixityPosition::Prefix, operator.into()),
                Fixity {
                    declaration: None,
                    form: FixityForm::Prefix,
                    precedence,
                },
            );
        }
        Self::from_entries(entries)
    }

    pub fn for_module(interface: &PackageInterface) -> Self {
        let mut table = Self::with_prelude();
        for definition in &interface.definitions {
            let ParsedHeader::Fixity(header) = &definition.syntax.header else {
                continue;
            };
            let position = if header.form.is_prefix() {
                FixityPosition::Prefix
            } else {
                FixityPosition::Infix
            };
            table.entries.insert(
                (position, header.operator.clone()),
                Fixity {
                    declaration: Some(definition.key),
                    form: header.form,
                    precedence: header.precedence,
                },
            );
        }
        table.refresh_fingerprint();
        table
    }

    pub fn infix(&self, operator: &str) -> Option<&Fixity> {
        self.entries.get(&(FixityPosition::Infix, operator.into()))
    }

    pub fn prefix(&self, operator: &str) -> Option<&Fixity> {
        self.entries.get(&(FixityPosition::Prefix, operator.into()))
    }

    pub fn fingerprint(&self) -> Digest {
        self.fingerprint
    }

    fn from_entries(entries: BTreeMap<(FixityPosition, String), Fixity>) -> Self {
        let mut value = Self {
            entries,
            fingerprint: Digest::of_bytes(b""),
        };
        value.refresh_fingerprint();
        value
    }

    fn refresh_fingerprint(&mut self) {
        let mut bytes = b"grandiose-stage0-fixity-v1".to_vec();
        for ((position, operator), fixity) in &self.entries {
            bytes.push(match position {
                FixityPosition::Prefix => 0,
                FixityPosition::Infix => 1,
            });
            bytes.extend_from_slice(&(operator.len() as u64).to_le_bytes());
            bytes.extend_from_slice(operator.as_bytes());
            bytes.push(match fixity.form {
                FixityForm::Prefix => 0,
                FixityForm::InfixLeft => 1,
                FixityForm::InfixRight => 2,
                FixityForm::InfixNonAssociative => 3,
            });
            bytes.push(fixity.precedence);
            match fixity.declaration {
                Some(key) => bytes.extend_from_slice(&key.0.as_bytes()),
                None => bytes.extend_from_slice(&[0; 32]),
            }
        }
        self.fingerprint = Digest::of_bytes(&bytes);
    }
}
