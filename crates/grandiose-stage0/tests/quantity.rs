use grandiose_stage0::Quantity;

#[test]
fn quantities_distinguish_sequence_exclusive_branches_and_replay() {
    assert_eq!(
        Quantity::ONCE.sequence(Quantity::ONCE).unwrap().upper,
        Some(2)
    );
    assert_eq!(Quantity::ONCE.branch_hull(Quantity::ZERO), Quantity::AFFINE);
    assert_eq!(
        Quantity::ONCE.multiply(Quantity::ONCE).unwrap(),
        Quantity::ONCE
    );
    assert_eq!(
        Quantity::UNRESTRICTED.multiply(Quantity::ZERO).unwrap(),
        Quantity::ZERO
    );
}

#[test]
fn principal_use_intervals_accept_only_contained_actual_use() {
    assert!(Quantity::AFFINE.contains(Quantity::ZERO));
    assert!(Quantity::AFFINE.contains(Quantity::ONCE));
    assert!(!Quantity::AFFINE.contains(Quantity::ONCE.sequence(Quantity::ONCE).unwrap()));
    assert!(Quantity::ONCE.requires_positive_use());
    assert!(!Quantity::ZERO.requires_positive_use());
}
