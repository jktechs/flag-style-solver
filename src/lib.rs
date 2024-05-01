use std::{fmt::Display, sync::Arc};

use logic::{BlockProof, DynLogic, False, LineProof, Logic, Proof, ProofBranch};

pub mod logic;

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Invert(pub Logic);
impl DynLogic for Invert {
    fn invert(self: Arc<Self>) -> Logic {
        self.0.clone()
    }
    fn intro(self: Arc<Self>, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    fn elim(self: Arc<Self>, proof: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Line(LineProof::new(
            False.wrap(),
            scope.clone(),
            [
                ProofBranch::Possible(self.0.clone()),
                ProofBranch::One(proof.clone()),
            ],
        ))]
    }
    logic_eq! {}
}
impl Display for Invert {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "¬{}", self.0)
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Variable(pub usize);
impl DynLogic for Variable {
    fn invert(self: Arc<Self>) -> Logic {
        Invert(self.wrap_rc()).wrap()
    }
    fn intro(self: Arc<Self>, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    fn elim(self: Arc<Self>, _: &Proof, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    logic_eq! {}
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", (self.0 as u8 + b'A') as char)
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Conj(pub Logic, pub Logic);
impl DynLogic for Conj {
    fn invert(self: Arc<Self>) -> Logic {
        Invert(self.wrap_rc()).wrap()
    }
    fn intro(self: Arc<Self>, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Line(LineProof::new(
            self.clone().wrap_rc(),
            scope.clone(),
            [
                ProofBranch::Possible(self.0.clone()),
                ProofBranch::Possible(self.1.clone()),
            ],
        ))]
    }
    fn elim(self: Arc<Self>, child: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![
            Proof::Line(LineProof::new(
                self.0.clone(),
                scope.clone(),
                [ProofBranch::One(child.clone())],
            )),
            Proof::Line(LineProof::new(
                self.1.clone(),
                scope.clone(),
                [ProofBranch::One(child.clone())],
            )),
        ]
    }
    logic_eq! {}
}
impl Display for Conj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}∧{})", self.0, self.1)
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Disj(pub Logic, pub Logic);
impl DynLogic for Disj {
    fn invert(self: Arc<Self>) -> Logic {
        Invert(self.wrap_rc()).wrap()
    }
    fn intro(self: Arc<Self>, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![
            Proof::Block(BlockProof::new(
                self.0.clone().0.invert(),
                self.clone().wrap_rc(),
                scope.clone(),
                ProofBranch::Possible(self.1.clone()),
            )),
            Proof::Block(BlockProof::new(
                self.1.clone().0.invert(),
                self.clone().wrap_rc(),
                scope.clone(),
                ProofBranch::Possible(self.0.clone()),
            )),
        ]
    }
    fn elim(self: Arc<Self>, child: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![
            Proof::Line(LineProof::new(
                self.0.clone(),
                scope.clone(),
                [
                    ProofBranch::One(child.clone()),
                    ProofBranch::Possible(self.1.clone().0.invert()),
                ],
            )),
            Proof::Line(LineProof::new(
                self.1.clone(),
                scope.clone(),
                [
                    ProofBranch::One(child.clone()),
                    ProofBranch::Possible(self.0.clone().0.invert()),
                ],
            )),
        ]
    }
    logic_eq! {}
}
impl Display for Disj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}∨{})", self.0, self.1)
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Impl(pub Logic, pub Logic);
impl DynLogic for Impl {
    fn invert(self: Arc<Self>) -> Logic {
        Invert(self.wrap_rc()).wrap()
    }
    fn intro(self: Arc<Self>, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Block(BlockProof::new(
            self.0.clone(),
            self.clone().wrap_rc(),
            scope.clone(),
            ProofBranch::Possible(self.1.clone()),
        ))]
    }
    fn elim(self: Arc<Self>, child: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Line(LineProof::new(
            self.1.clone(),
            scope.clone(),
            [
                ProofBranch::One(child.clone()),
                ProofBranch::Possible(self.0.clone()),
            ],
        ))]
    }
    logic_eq! {}
}
impl Display for Impl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}⇒{})", self.0, self.1)
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct Bicond(pub Logic, pub Logic);
impl DynLogic for Bicond {
    fn invert(self: Arc<Self>) -> Logic {
        Invert(self.wrap_rc()).wrap()
    }
    fn intro(self: Arc<Self>, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Line(LineProof::new(
            self.clone().wrap_rc(),
            scope.clone(),
            [
                ProofBranch::Possible(Impl(self.0.clone(), self.1.clone()).wrap()),
                ProofBranch::Possible(Impl(self.1.clone(), self.0.clone()).wrap()),
            ],
        ))]
    }
    fn elim(self: Arc<Self>, child: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::Line(LineProof::new(
            self.1.clone(),
            scope.clone(),
            [
                ProofBranch::One(child.clone()),
                ProofBranch::Possible(self.0.clone()),
            ],
        ))]
    }
    logic_eq! {}
}
impl Display for Bicond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}⇔{})", self.0, self.1)
    }
}
