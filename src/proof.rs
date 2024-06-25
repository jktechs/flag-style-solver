//! This module makes a framework for proving logical expressions.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    sync::{Arc, Mutex, OnceLock},
};

use crate::{
    expressions::{Cashe, DynExpression, Expression},
    proposition::{False, Inv, True},
};

#[derive(Debug, Clone)]
/// A linked list of all current assumptions.
pub struct Scope(Arc<(Expression, Option<Scope>)>);
impl PartialEq for Scope {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for Scope {}
impl Hash for Scope {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}
impl Scope {
    #[must_use]
    /// Creates a `Scope` were only truth is assumed.
    pub fn empty() -> Self {
        let truth = True.wrap();
        Self(Arc::new((truth, None)))
    }
    #[must_use]
    /// Returns a new scope with the extra assumption.
    pub fn extend(&self, assumption: Expression) -> Option<Self> {
        if self.contains(&assumption) {
            None
        } else {
            Some(Self(Arc::new((assumption, Some(self.clone())))))
        }
    }
    #[must_use]
    /// Returns a refrence to the assumption that was last added.
    pub fn assumption(&self) -> &Expression {
        &self.0 .0
    }
    /// Returns the parrent scope.
    fn parrent(&self) -> Option<&Scope> {
        self.0 .1.as_ref()
    }
    #[must_use]
    /// Tries to prove the target via elimination on assumptions.
    pub fn proof(&self, target: &Expression, scope: &Scope) -> Option<Proof> {
        let mut elim = move || Some(Proof::assum(scope, self));
        if self.assumption() == target {
            return elim();
        }
        if let Some(proof) = self.parrent().and_then(|p| p.proof(target, scope)) {
            return Some(proof);
        }
        if let Some(proof) = self.assumption().elimination(scope, target, &mut elim) {
            return Some(proof);
        }
        None
    }
    /// Tests if a certain expression is assumed.
    fn contains(&self, expr: &Expression) -> bool {
        if self.assumption() == expr {
            true
        } else if let Some(parrent) = self.parrent() {
            parrent.contains(expr)
        } else {
            false
        }
    }
    /// The amount of assumptions made.
    fn len(&self) -> usize {
        self.parrent().map(Self::len).unwrap_or_default() + 1
    }
}
/// A logical expression that may or may not be proven already.
pub enum MaybeProven {
    /// An unproven expression.
    Unproven(Expression),
    /// A proof for the expression.
    Proven(Proof),
}
impl MaybeProven {
    #[must_use]
    /// The expression that may or may not be proven.
    pub fn expression(&self) -> &Expression {
        match self {
            Self::Proven(p) => &p.expression,
            Self::Unproven(e) => e,
        }
    }
    #[must_use]
    /// Makes sure there is a proof.
    pub fn proof(self, scope: &Scope) -> Option<Proof> {
        match self {
            Self::Proven(p) => Some(p),
            Self::Unproven(e) => Proof::new(&e, scope),
        }
    }
}
#[derive(Debug)]
/// A proof of a logical expression.
pub struct Proof {
    /// The scope under which this proof exists.
    scope: Scope,
    /// The expression to be proven.
    expression: Expression,
    /// The details of the specific proof method.
    proof_type: Box<Type>,
}
impl Proof {
    #[must_use]
    /// Tries to prove the `Expression` under the `Scope` using any method.
    pub fn new(expr: &Expression, scope: &Scope) -> Option<Proof> {
        /// A cashe for all things that are currently being prooved.
        static PROOF_CASHE: Cashe<Expression, HashSet<Scope>> = OnceLock::new();

        if let Ok(mut cashe) = PROOF_CASHE.get_or_init(Mutex::default).lock() {
            if let Some(scopes) = cashe.get(expr) {
                if scopes.contains(scope) {
                    return None;
                }
            }
            cashe.entry(expr.clone()).or_default().insert(scope.clone());
        }

        if let Some(proof) = expr.introduction(scope) {
            Some(proof)
        } else if let Some(proof) = scope.proof(expr, scope) {
            Some(proof)
        } else if *expr != False.wrap() {
            Proof::flag(scope, &expr.invert(), &False.wrap(), expr, "RAA")
        } else {
            None
        }
    }
    #[must_use]
    /// Creates a flag-proof with an assumption.
    pub fn flag(
        scope: &Scope,
        assum: &Expression,
        root: &Expression,
        expression: &Expression,
        reason: &'static str,
    ) -> Option<Proof> {
        let scope = scope.extend(assum.clone())?;
        Some(Proof {
            proof_type: Box::new(Type::Flag(Proof::new(root, &scope)?, reason)),
            expression: expression.clone(),
            scope,
        })
    }
    #[must_use]
    /// Creates a line-proof dependent on multiple other expressions.
    pub fn line(
        scope: &Scope,
        lines: Vec<MaybeProven>,
        expression: &Expression,
        reason: &'static str,
    ) -> Option<Proof> {
        Some(Proof {
            scope: scope.clone(),
            expression: expression.clone(),
            proof_type: Box::new(Type::Line(
                lines
                    .into_iter()
                    .map(|e| e.proof(scope))
                    .try_fold(Vec::new(), |mut x, y| {
                        x.push(y?);
                        Some(x)
                    })?,
                reason,
            )),
        })
    }
    #[must_use]
    /// Creates an assumption-proof based on a previous assumption.
    pub fn assum(scope: &Scope, origin: &Scope) -> Proof {
        Proof {
            scope: scope.clone(),
            expression: origin.assumption().clone(),
            proof_type: Box::new(Type::Assum(origin.clone())),
        }
    }
}
#[derive(Debug)]
/// Different types of proofs.
enum Type {
    /// Proof under a certain assumption.
    Flag(Proof, &'static str),
    /// Proof using multiple other proofs.
    Line(Vec<Proof>, &'static str),
    /// Proof using a assumption directly.
    Assum(Scope),
}

/// Turns the abstract tree of a proof into semi human readable text.
/// # Errors
/// when a write to the formatter gives an error.
fn format<W: std::fmt::Write>(
    proof: &Proof,
    f: &mut W,
    indent: usize,
    mut line: usize,
    line_cashe: &mut HashMap<Scope, usize>,
) -> Result<(usize, usize), std::fmt::Error> {
    let padding = "| ".repeat(indent);
    let location;
    match &*proof.proof_type {
        Type::Assum(a) => {
            location = line_cashe.get(a).copied().unwrap_or(999);
        }
        Type::Flag(flag, reason) => {
            // writeln!(f, "   {padding}{{ assuming }}")?;
            line_cashe.insert(proof.scope.clone(), line);
            let flag_line = line;
            writeln!(f, "{line:2} {padding}[ {} ]", proof.scope.assumption())?;
            line += 1;
            let expr_line;
            (line, expr_line) = format(flag, f, indent + 1, line, line_cashe)?;
            writeln!(f, "   {padding}{{ {reason}: {flag_line}, {expr_line},  }}")?;
            location = line;
            writeln!(f, "{line:2} {padding}{}", proof.expression)?;
            line += 1;
        }
        Type::Line(l, reason) => {
            let mut lines = String::new();
            for i in l {
                let to_push;
                (line, to_push) = format(i, f, indent, line, line_cashe)?;
                lines.push_str(&format!("{to_push}, "));
            }
            writeln!(f, "   {padding}{{ {reason}: {lines} }}")?;
            location = line;
            writeln!(f, "{line:2} {padding}{}", proof.expression)?;
            line += 1;
        }
    }
    Ok((line, location))
}
impl Display for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        format(self, f, 0, 0, &mut HashMap::new())?;
        Ok(())
    }
}
