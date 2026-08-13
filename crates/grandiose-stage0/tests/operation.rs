use grandiose_stage0::{Budget, CancellationToken, PublicationGuard};

#[test]
fn child_budget_cannot_exceed_itself_or_its_parent() {
    let root = Budget::root("request", 10);
    let child = root.child("parser", 7);
    child.charge(7).unwrap();
    assert!(child.charge(1).is_err());
    assert_eq!(root.spent(), 7);
    child.release(7);
    assert_eq!(root.spent(), 0);
    assert!(root.charge(11).is_err());
}

#[test]
fn failed_child_charge_rolls_back_the_parent_reservation() {
    let root = Budget::root("request", 10);
    let child = root.child("solver", 2);
    assert!(child.charge(3).is_err());
    assert_eq!(root.spent(), 0);
    assert_eq!(child.spent(), 0);
}

#[test]
fn cancelled_requests_cannot_publish_staged_products() {
    let token = CancellationToken::new();
    token.cancel();
    assert!(PublicationGuard::stage("artifact").commit(&token).is_err());
}
