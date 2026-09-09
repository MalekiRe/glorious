//! Source-defined operator fixities and deterministic body grouping inputs.
//!
//! Bodies deliberately retain flat operator chains.  This table is built from
//! their owning module interface after all declaration headers are available;
//! no parser heuristic is permitted to choose associativity or precedence.

use std::collections::{BTreeMap, BTreeSet};

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
    pub explicit_target: bool,
    pub target: Option<DefKey>,
    /// Includes the selected declaration contract, including a private
    /// target exposed only through an exported operator binding.
    pub target_contract: Option<Digest>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixityTable {
    entries: BTreeMap<(FixityPosition, String), Fixity>,
    ambiguous: BTreeSet<(FixityPosition, String)>,
    fingerprint: Digest,
}

impl FixityTable {
    /// Empty until source declarations/imports populate the operator table.
    /// Kept as a constructor name for existing API consumers; there is no
    /// implicit compiler prelude and no privileged operator spelling.
    pub fn with_prelude() -> Self {
        Self::from_entries(BTreeMap::new())
    }
    pub fn for_module(interface: &PackageInterface) -> Self {
        let mut table = Self::with_prelude();
        let index = crate::DefinitionIndex::from_interface(interface);
        for definition in &interface.definitions {
            let ParsedHeader::Fixity(header) = &definition.syntax.header else {
                continue;
            };
            table.insert_declared(definition.key, header, &index);
        }
        table.freeze();
        table
    }

    /// Resolve declaration visibility before grouping bodies, including
    /// imported operators and independent prefix/infix declarations.
    pub fn visible_in_module(
        module: &crate::ModuleKey,
        index: &crate::DefinitionIndex,
        declarations: &BTreeMap<DefKey, crate::FixityHeader>,
    ) -> Self {
        let mut table = Self::with_prelude();
        for (definition, header) in declarations {
            let path = vec![header.operator.clone()];
            match index.resolve_path(crate::DefinitionNamespace::Operator, module, &path) {
                crate::ResolutionState::Resolved(candidate) if candidate == *definition => {
                    table.insert_declared(*definition, header, index);
                }
                crate::ResolutionState::Ambiguous(candidates) if candidates.contains(definition) => {
                    let same_position = candidates.iter().filter(|candidate| {
                        declarations.get(candidate).is_some_and(|candidate|
                            candidate.form.is_prefix() == header.form.is_prefix())
                    }).count();
                    if same_position == 1 {
                        table.insert_declared(*definition, header, index);
                    } else {
                        table.mark_ambiguous(header);
                    }
                }
                _ => {}
            }
        }
        table.freeze();
        table
    }

    /// Extend a module table with a declaration already proven visible by the
    /// module resolver. Imports and globs are resolved before this point, so
    /// the caller supplies the source spelling that is in scope.
    pub(crate) fn insert_declared(&mut self, declaration: DefKey, header: &crate::FixityHeader, index: &crate::DefinitionIndex) {
        let target = header.target.as_ref().and_then(|path| {
            let owner = index.owner(declaration)?;
            match index.resolve_path(crate::DefinitionNamespace::Value, owner, path) {
                crate::ResolutionState::Resolved(target) => Some(target),
                _ => None,
            }
        });
        let position = if header.form.is_prefix() {
            FixityPosition::Prefix
        } else {
            FixityPosition::Infix
        };
        self.entries.insert(
            (position, header.operator.clone()),
            Fixity {
                declaration: Some(declaration),
                form: header.form,
                precedence: header.precedence,
                explicit_target: header.target.is_some(),
                target,
                target_contract: target.map(|target| index.definition_contract_fingerprint(target)),
            },
        );
    }

    /// Seal a table after every locally declared and resolver-visible import
    /// has been inserted. This keeps the fingerprint sensitive to imported
    /// fixities, not merely the owning source file.
    pub(crate) fn freeze(&mut self) {
        self.refresh_fingerprint();
    }

    pub(crate) fn dependency_modules(&self, index: &crate::DefinitionIndex, module: &crate::ModuleKey) -> Vec<crate::ModuleKey> {
        let mut modules = BTreeSet::from([module.clone()]);
        for fixity in self.entries.values() {
            if let Some(declaration) = fixity.declaration {
                modules.extend(index.definition_contract_dependencies(declaration, module));
            }
        }
        modules.into_iter().collect()
    }

    /// Retain an import-level ambiguity instead of degrading it into an
    /// absent declaration. Bodies can then distinguish a missing fixity from
    /// two visible declarations which cannot be selected deterministically.
    pub(crate) fn mark_ambiguous(&mut self, header: &crate::FixityHeader) {
        let position = if header.form.is_prefix() {
            FixityPosition::Prefix
        } else {
            FixityPosition::Infix
        };
        self.ambiguous.insert((position, header.operator.clone()));
    }

    pub fn infix(&self, operator: &str) -> Option<&Fixity> {
        self.entries.get(&(FixityPosition::Infix, operator.into()))
    }

    pub fn prefix(&self, operator: &str) -> Option<&Fixity> {
        self.entries.get(&(FixityPosition::Prefix, operator.into()))
    }

    pub fn infix_is_ambiguous(&self, operator: &str) -> bool {
        self.ambiguous
            .contains(&(FixityPosition::Infix, operator.into()))
    }

    pub fn prefix_is_ambiguous(&self, operator: &str) -> bool {
        self.ambiguous
            .contains(&(FixityPosition::Prefix, operator.into()))
    }

    pub fn fingerprint(&self) -> Digest {
        self.fingerprint
    }

    fn from_entries(entries: BTreeMap<(FixityPosition, String), Fixity>) -> Self {
        let mut value = Self {
            entries,
            ambiguous: BTreeSet::new(),
            fingerprint: Digest::of_bytes(b""),
        };
        value.refresh_fingerprint();
        value
    }

    fn refresh_fingerprint(&mut self) {
        let mut bytes = b"grandiose-stage0-fixity-v2".to_vec();
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
            bytes.push(u8::from(fixity.explicit_target));
            match fixity.target {
                Some(key) => { bytes.push(1); bytes.extend_from_slice(key.0.as_bytes().as_slice()); }
                None => bytes.push(0),
            }
            match fixity.target_contract {
                Some(contract) => { bytes.push(1); bytes.extend_from_slice(contract.as_bytes().as_slice()); }
                None => bytes.push(0),
            }
        }
        for (position, operator) in &self.ambiguous {
            bytes.push(2);
            bytes.push(match position {
                FixityPosition::Prefix => 0,
                FixityPosition::Infix => 1,
            });
            bytes.extend_from_slice(&(operator.len() as u64).to_le_bytes());
            bytes.extend_from_slice(operator.as_bytes());
        }
        self.fingerprint = Digest::of_bytes(&bytes);
    }
}
