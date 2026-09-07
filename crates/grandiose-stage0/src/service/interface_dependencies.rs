//! Dependency evidence for already-resolved, possibly cyclic public interfaces.
//!
//! Import/reexport cycles are resolved before publication. Collapse each module
//! SCC's internal interface edges to its complete source-input set, retaining
//! every outgoing interface edge. The general dependency ledger remains strict
//! about cycles in products which have no such fixed-point semantics.

use crate::{DependencyNode, FileKey, ModuleKey};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn publication_dependencies(
    modules: &BTreeMap<ModuleKey, (FileKey, Vec<ModuleKey>)>,
) -> BTreeMap<ModuleKey, Vec<DependencyNode>> {
    let reachable = modules
        .keys()
        .map(|origin| {
            let mut seen = BTreeSet::new();
            let mut pending = vec![origin.clone()];
            while let Some(module) = pending.pop() {
                if seen.insert(module.clone()) {
                    if let Some((_, dependencies)) = modules.get(&module) {
                        pending.extend(dependencies.iter().cloned());
                    }
                }
            }
            (origin.clone(), seen)
        })
        .collect::<BTreeMap<_, _>>();

    modules
        .keys()
        .map(|origin| {
            let component = reachable[origin]
                .iter()
                .filter(|module| {
                    reachable
                        .get(*module)
                        .is_some_and(|back| back.contains(origin))
                })
                .cloned()
                .collect::<BTreeSet<_>>();
            let mut dependencies = BTreeSet::new();
            for member in &component {
                let (file, outgoing) = &modules[member];
                dependencies.insert(DependencyNode::Input(*file));
                dependencies.extend(
                    outgoing
                        .iter()
                        .filter(|module| !component.contains(*module))
                        .cloned()
                        .map(DependencyNode::Interface),
                );
            }
            (origin.clone(), dependencies.into_iter().collect())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PackageKey;

    fn module(name: &str) -> ModuleKey {
        ModuleKey {
            package: PackageKey("dependencies@0.1.0".into()),
            path: name.into(),
        }
    }
    fn file(name: &str) -> FileKey {
        FileKey::new(&PackageKey("dependencies@0.1.0".into()), name)
    }

    #[test]
    fn a_cycle_retains_all_member_inputs_and_outgoing_interfaces() {
        let graph = BTreeMap::from([
            (module("a"), (file("a"), vec![module("b")])),
            (
                module("b"),
                (file("b"), vec![module("c"), module("external")]),
            ),
            (module("c"), (file("c"), vec![module("a")])),
            (module("external"), (file("external"), vec![])),
        ]);
        let actual = publication_dependencies(&graph);
        let expected = BTreeSet::from([
            DependencyNode::Input(file("a")),
            DependencyNode::Input(file("b")),
            DependencyNode::Input(file("c")),
            DependencyNode::Interface(module("external")),
        ]);
        for name in ["a", "b", "c"] {
            assert_eq!(
                actual[&module(name)]
                    .iter()
                    .cloned()
                    .collect::<BTreeSet<_>>(),
                expected
            );
        }
        assert_eq!(
            actual[&module("external")],
            vec![DependencyNode::Input(file("external"))]
        );
    }

    #[test]
    fn acyclic_and_missing_interface_edges_are_not_erased() {
        let graph = BTreeMap::from([
            (module("a"), (file("a"), vec![module("b")])),
            (module("b"), (file("b"), vec![module("missing")])),
        ]);
        let actual = publication_dependencies(&graph);
        assert!(actual[&module("a")].contains(&DependencyNode::Interface(module("b"))));
        assert!(actual[&module("b")].contains(&DependencyNode::Interface(module("missing"))));
    }
}
