//! This module makes a framework for storing logical expressions in a single concrete type: `Expression`.

use std::{
    any::Any,
    collections::HashMap,
    fmt::{Debug, Display, Pointer},
    hash::{Hash, Hasher},
    sync::{Arc, Mutex, OnceLock, Weak},
};

use crate::proof::{Proof, Scope};

/// A cashe of key and value pairs.
pub type Cashe<K, V> = OnceLock<Mutex<HashMap<K, V>>>;

/// This trait adds the `as_any` function to all static and `Sized` types.
pub trait AsAny {
    /// Casts the `self` refrence into a `dyn Any` refrence.
    fn as_any(&self) -> &dyn Any;
}
impl<T: 'static + Sized> AsAny for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

/// A version of the `Hash` trait that can be made into a dynamic object.
pub trait DynHash {
    /// The same as the `hash` function in `Hash` but without generics.
    fn dyn_hash(&self, state: &mut dyn Hasher);
}
impl<H: Hash> DynHash for H {
    fn dyn_hash(&self, mut state: &mut dyn Hasher) {
        self.hash(&mut state);
    }
}
impl Hash for dyn DynHash {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.dyn_hash(state);
    }
}
/// A version of the `Eq` trait that can be made into a dynamic object.
///
/// This makes use of the `AsAny` trait for downcasting.
pub trait DynEq: AsAny {
    /// A version of the `eq` function on `PartialEq` where `other` can be a `dyn Any`.
    fn dyn_eq(&self, other: &dyn Any) -> bool;
}
impl<T: Eq + AsAny + 'static> DynEq for T {
    fn dyn_eq(&self, other: &dyn Any) -> bool {
        if let Some(other) = other.downcast_ref::<Self>() {
            self == other
        } else {
            false
        }
    }
}
impl PartialEq for dyn DynEq {
    fn eq(&self, other: &Self) -> bool {
        self.dyn_eq(other.as_any())
    }
}
impl Eq for dyn DynEq {}

/// A logical expression that can be made into a dynamic object.
pub trait DynExpression: DynHash + DynEq + Display + Send + Sync + 'static {
    /// Wraps the concrete type into the `Expression` object.
    ///
    /// This also uses an internal cashe.
    fn wrap(self) -> Expression
    where
        Self: Sized,
    {
        Arc::new(self).wrap_rc()
    }
    /// Wraps an `Arc` of the concrete type into the `Expression` object.
    ///
    /// This also uses an internal cashe.
    fn wrap_rc(self: Arc<Self>) -> Expression
    where
        Self: Sized,
    {
        /// A cashe for stroing expression for reuse.
        static CASHE: Cashe<Expression, Weak<dyn DynExpression>> = OnceLock::new();

        let tmp = Expression(self);
        if let Ok(mut cashe) = CASHE.get_or_init(Mutex::default).lock() {
            if let Some(cashed) = cashe.get(&tmp) {
                if let Some(cloned) = cashed.upgrade() {
                    drop(tmp);
                    return Expression(cloned);
                }
                cashe.remove(&tmp);
            }
            cashe.insert(tmp.clone(), Arc::downgrade(&tmp.0));
        }
        tmp
    }
    /// Returns the logical inverse of self.
    fn invert(self: Arc<Self>) -> Expression;
    /// Gives an introduction proof of this expression if possible.
    fn introduction(self: Arc<Self>, scope: &Scope) -> Option<Proof>;
    /// tries to eliminate this expression in order to prove the target by suppling a proof for self.
    fn elimination(
        self: Arc<Self>,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof>;
}
/// Handles the logic for eliminating an expression imediatly or passing the target on.
pub fn eliminate(
    expr: Expression,
    target: &Expression,
    scope: &Scope,
    proof: &mut dyn FnMut(Expression) -> Option<Proof>,
) -> Option<Proof> {
    if expr == *target {
        proof(expr)
    } else {
        let expr_ref = &expr;
        expr.elimination(scope, target, &mut move || proof(expr_ref.clone()))
    }
}

#[derive(Clone)]
/// A logical expression.
pub struct Expression(Arc<dyn DynExpression>);
impl Expression {
    #[must_use]
    /// Returns the logical inverse of self.
    pub fn invert(&self) -> Expression {
        self.clone().0.invert()
    }
    #[must_use]
    /// Gives an introduction proof of this expression if possible.
    pub fn introduction(&self, scope: &Scope) -> Option<Proof> {
        self.clone().0.introduction(scope)
    }
    #[must_use]
    /// tries to eliminate this expression in order to prove the target by suppling a proof for self.
    pub fn elimination(
        &self,
        scope: &Scope,
        target: &Expression,
        proof: &mut dyn FnMut() -> Option<Proof>,
    ) -> Option<Proof> {
        self.clone().0.elimination(scope, target, proof)
    }
}
impl Hash for Expression {
    fn hash<H: Hasher>(&self, mut state: &mut H) {
        self.0.dyn_hash(&mut state);
    }
}
impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        let p = (*other.0).as_any();
        self.0.dyn_eq(p)
    }
}
impl Eq for Expression {}
impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Arc<_> as Display>::fmt(&self.0, f)
    }
}
impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Arc<_> as Display>::fmt(&self.0, f)
    }
}
impl Pointer for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Arc<_> as Pointer>::fmt(&self.0, f)
    }
}
