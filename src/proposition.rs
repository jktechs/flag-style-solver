//! This module defines all needed operators to express Propositional expressions.

use std::{any::Any, fmt::Display, sync::Arc};

use crate::{
    expressions::{eliminate, DynExpression, Expression},
    proof::{MaybeProven, Proof, Scope},
};

#[derive(Hash, PartialEq, Eq)]
/// This represents Truth and as such is the weakest logical value that can be proven.
pub struct True;
impl Display for True {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "⊤")
    }
}

impl DynExpression for True {
    fn invert(self: Arc<Self>) -> Expression {
        False.wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        None
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        None
    }
}

#[derive(Hash, PartialEq, Eq)]
/// This represents The idea of a contridiction and as such can be used to prove anything.
pub struct False;
impl Display for False {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "⊥")
    }
}

impl DynExpression for False {
    fn invert(self: Arc<Self>) -> Expression {
        True.wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        None
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        Proof::line(scope, vec![MaybeProven::Proven(proof()?)], target, "⊥-elim")
    }
}

#[derive(Hash, PartialEq, Eq)]
/// This represents an inversion of its child expression.
pub struct Inv(pub Expression);
impl DynExpression for Inv {
    fn invert(self: Arc<Self>) -> Expression {
        self.0.clone()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        Proof::flag(
            scope,
            &self.clone().invert(),
            &False.wrap(),
            &self.wrap_rc(),
            "¬-intro",
        )
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        eliminate(False.wrap(), target, scope, &mut move |e| {
            Proof::line(
                scope,
                vec![
                    MaybeProven::Proven(proof()?),
                    MaybeProven::Unproven(self.0.clone()),
                ],
                &e,
                "¬-elim",
            )
        })
    }
}
impl Display for Inv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "¬{}", self.0)
    }
}

#[derive(Hash, PartialEq, Eq)]
/// This represents a "conjunction" of its children, so for this to be true all of its children have to be aswel.
pub struct Conj(pub Expression, pub Expression);
impl DynExpression for Conj {
    fn invert(self: Arc<Self>) -> Expression {
        Inv(self.wrap_rc()).wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        Proof::line(
            scope,
            vec![
                MaybeProven::Unproven(self.0.clone()),
                MaybeProven::Unproven(self.1.clone()),
            ],
            &self.wrap_rc(),
            "∧-intro",
        )
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        let mut func =
            move |e| Proof::line(scope, vec![MaybeProven::Proven(proof()?)], &e, "∧-elim");
        if let Some(proof) = eliminate(self.0.clone(), target, scope, &mut func) {
            return Some(proof);
        }
        eliminate(self.1.clone(), target, scope, &mut func)
    }
}
impl Display for Conj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}∧{})", self.0, self.1)
    }
}

#[derive(Hash, PartialEq, Eq)]
/// This represents an "Implication", so its only true if when its first child is true its other is aswel.
pub struct Impl(pub Expression, pub Expression);
impl DynExpression for Impl {
    fn invert(self: Arc<Self>) -> Expression {
        Inv(self.wrap_rc()).wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        Proof::flag(scope, &self.0, &self.1, &self.clone().wrap_rc(), "⇒-intro")
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        eliminate(self.1.clone(), target, scope, &mut move |e| {
            Proof::line(
                scope,
                vec![
                    MaybeProven::Proven(proof()?),
                    MaybeProven::Unproven(self.0.clone()),
                ],
                &e,
                "⇒-elim",
            )
        })
    }
}
impl Display for Impl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}⇒{})", self.0, self.1)
    }
}
#[derive(Hash, PartialEq, Eq)]
/// This represents an "Disjunction" of its children, so it is true if one or more if its children are.
pub struct Disj(pub Expression, pub Expression);
impl DynExpression for Disj {
    fn invert(self: Arc<Self>) -> Expression {
        Inv(self.wrap_rc()).wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        let this = &self.clone().wrap_rc();
        if let Some(proof) = Proof::flag(scope, &self.0.invert(), &self.1, this, "∨-intro") {
            Some(proof)
        } else {
            Proof::flag(scope, &self.1.invert(), &self.0, this, "∨-intro")
        }
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        mut proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        let proof_b = &mut proof;
        let this = self.clone();
        if let Some(proof) = eliminate(self.0.clone(), target, scope, &mut move |e| {
            Proof::line(
                scope,
                vec![
                    MaybeProven::Proven(proof_b()?),
                    MaybeProven::Unproven(self.1.invert()),
                ],
                &e,
                "∨-elim",
            )
        }) {
            return Some(proof);
        }
        eliminate(this.1.clone(), target, scope, &mut move |e| {
            Proof::line(
                scope,
                vec![
                    MaybeProven::Proven(proof()?),
                    MaybeProven::Unproven(this.0.invert()),
                ],
                &e,
                "∨-elim",
            )
        })
    }
}
impl Display for Disj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}∨{})", self.0, self.1)
    }
}
#[derive(Hash, PartialEq, Eq)]
/// This represents a "Biconditional" of its children, so its only true if both its children are the same.
pub struct Bicond(pub Expression, pub Expression);
impl DynExpression for Bicond {
    fn invert(self: Arc<Self>) -> Expression {
        Inv(self.wrap_rc()).wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        Proof::line(
            scope,
            vec![
                MaybeProven::Unproven(Impl(self.0.clone(), self.1.clone()).wrap()),
                MaybeProven::Unproven(Impl(self.1.clone(), self.0.clone()).wrap()),
            ],
            &self.clone().wrap_rc(),
            "⇔-intro",
        )
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        let mut func =
            move |e| Proof::line(scope, vec![MaybeProven::Proven(proof()?)], &e, "⇔-elim");
        if let Some(proof) = eliminate(
            Impl(self.0.clone(), self.1.clone()).wrap(),
            target,
            scope,
            &mut func,
        ) {
            return Some(proof);
        }
        eliminate(
            Impl(self.1.clone(), self.0.clone()).wrap(),
            target,
            scope,
            &mut func,
        )
    }
}
impl Display for Bicond {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}⇔{})", self.0, self.1)
    }
}
#[derive(Hash, PartialEq, Eq)]
/// This represents a propositional variable.
pub struct Var(pub char);
impl DynExpression for Var {
    fn invert(self: Arc<Self>) -> Expression {
        Inv(self.wrap_rc()).wrap()
    }
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof> {
        None
    }
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        None
    }
}
impl Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
