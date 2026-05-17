// Test case from issue #151284.
// Make sure that private types indirectly leaked through RPIT don't result in missing MIR.

#![feature(rustc_attrs)]

pub trait ToPriv {
    type AssocPriv;
}

pub trait PubTr {
    #[expect(private_bounds)]
    type Assoc: ToPriv<AssocPriv = Priv>;
}

struct Dummy;
struct DummyToPriv;
impl PubTr for Dummy {
    type Assoc = DummyToPriv;
}
impl ToPriv for DummyToPriv {
    type AssocPriv = Priv;
}

pub fn get_dummy() -> impl PubTr {
    Dummy
}

#[rustc_effective_visibility]
struct Priv;
//~^ ERROR Direct: pub(crate), Reexported: pub(crate), Reachable: pub(crate), ReachableThroughImplTrait: pub
//~| ERROR Direct: pub(crate), Reexported: pub(crate), Reachable: pub(crate), ReachableThroughImplTrait: pub

#[rustc_effective_visibility]
impl Priv {
//~^ ERROR Direct: pub(crate), Reexported: pub(crate), Reachable: pub(crate), ReachableThroughImplTrait: pub
    #[rustc_effective_visibility]
    pub fn foo() {}
    //~^ ERROR Direct: pub(crate), Reexported: pub(crate), Reachable: pub(crate), ReachableThroughImplTrait: pub
}

fn main() {}
