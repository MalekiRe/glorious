use grandiose_compiler_base::{Digest, ModuleKey, PackageKey, Quantity, Safety};
use grandiose_compiler_base::identity::requester_has_lexical_authority;

#[test]
fn lexical_authority_never_uses_a_textual_or_cross_package_prefix() {
    let module = |package: &str, path: &str| ModuleKey {
        package: PackageKey(package.into()), path: path.into(),
    };
    let owner = module("a@1", "crate::inner");
    assert!(requester_has_lexical_authority(&owner, &owner));
    assert!(requester_has_lexical_authority(&module("a@1", "crate::inner::child"), &owner));
    assert!(!requester_has_lexical_authority(&module("a@1", "crate::innerish"), &owner));
    assert!(!requester_has_lexical_authority(&module("a@1", "crate"), &owner));
    assert!(!requester_has_lexical_authority(&module("b@1", "crate::inner::child"), &owner));
}

#[test]
fn shared_vocabulary_is_usable_without_the_compiler_or_syntax() {
    assert_ne!(Digest::of_parts([b"ab".as_slice(), b"c"]), Digest::of_parts([b"a".as_slice(), b"bc"]));
    assert!(Quantity::UNRESTRICTED.contains(Quantity::ONCE));
    assert_eq!(Safety::default(), Safety::Safe);
}
