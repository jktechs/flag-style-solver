#![allow(dead_code)]
use core::hash::Hash;
use std::{
    any::Any,
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hasher,
    sync::{Arc, Mutex},
    usize,
};

/// Macro for automaticly adding the eq function for the `DynLogic` struct.
#[macro_export]
macro_rules! logic_eq {
    () => {
        fn dyn_eq(&self, other: &dyn DynLogic) -> bool {
            let this = self.as_any().downcast_ref::<Self>();
            let other = other.as_any().downcast_ref::<Self>();
            this.zip(other).map_or(false, |(a, b)| a == b)
        }
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
    };
}
/// Macro for automaticly adding the invert function for the `DynLogic` struct.
#[macro_export]
macro_rules! logic_invert {
    () => {};
}

/// Dynamic version of the `Hash` trait.
pub trait DynHash {
    fn dyn_hash(&self, state: &mut dyn Hasher);
}
impl<T: Hash> DynHash for T {
    fn dyn_hash(&self, mut state: &mut dyn Hasher) {
        self.hash(&mut state);
    }
}
/// The interface for A logical statement.
/// This trait will most-allways look like this:
/// ```
/// use sat_again::{logic::{DynLogic, Logic, Proof, BlockProof}, Invert};
/// use std::{sync::Arc, any::Any, fmt::{Display, Formatter}};
///
/// #[derive(PartialEq, Hash)]
/// struct A;
/// impl Display for A { fn fmt(&self, _: &mut Formatter::<'_>) -> Result<(), std::fmt::Error> { todo!() } }
/// impl DynLogic for A {
///     fn dyn_eq(&self, other: &dyn DynLogic) -> bool {
///         let this = self.as_any().downcast_ref::<Self>();
///         let other = other.as_any().downcast_ref::<Self>();
///         this.zip(other).map_or(false, |(a, b)| a == b)
///     }
///     fn as_any(&self) -> &dyn Any {
///         self
///     }
///     fn invert(self: Arc<Self>) -> Logic {
///         Invert(self.wrap_rc()).wrap()
///     }
///     fn intro(self: Arc<Self>, _: &Arc<BlockProof>) -> Vec<Proof> { todo!() }
///     fn elim(self: Arc<Self>, _: &Proof, _: &Arc<BlockProof>) -> Vec<Proof> { todo!() }
/// }
/// ```
pub trait DynLogic: DynHash + Display + Send + Sync {
    /// The reason this isn't implemented by default is because:  
    /// Self needs to be the original type wich can not be accesed from the trait.
    fn dyn_eq(&self, other: &dyn DynLogic) -> bool;
    /// Returns a refrence to a `dyn Any`.
    /// This is used for casting between different Logic statements,  
    /// to check for equality.
    fn as_any(&self) -> &dyn Any;
    /// Returns the logical inverse of this statement.  
    /// This can not be implemented by default, because  
    /// `Self` needs to be `Sized` to convert to `dyn DynLogic`
    fn invert(self: Arc<Self>) -> Logic;
    /// Makes all posible intoduction-proofs for this statement.
    fn intro(self: Arc<Self>, scope: &Arc<BlockProof>) -> Vec<Proof>;
    /// Makes all posible proofs for this statement to be eliminated.
    /// where `child` is a proof for `self`
    fn elim(self: Arc<Self>, child: &Proof, scope: &Arc<BlockProof>) -> Vec<Proof>;
    /// If it should be tried to contridict this statement
    fn contridict(&self) -> bool {
        true
    }
    /// Turn a raw `Sized` `DynLogic` into a `Logic`
    fn wrap(self) -> Logic
    where
        Self: Sized + 'static,
    {
        Logic(Arc::new(self))
    }
    /// Turn a raw `Sized` refrence counted `DynLogic` into a `Logic`
    fn wrap_rc(self: Arc<Self>) -> Logic
    where
        Self: Sized + 'static,
    {
        Logic(self)
    }
}
/// The main container for a logic statement.
#[derive(Clone)]
pub struct Logic(pub Arc<dyn DynLogic>);
impl Hash for Logic {
    fn hash<H: Hasher>(&self, mut state: &mut H) {
        self.0.as_ref().dyn_hash(&mut state)
    }
}
impl Display for Logic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.as_ref())
    }
}
impl Debug for Logic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.as_ref())
    }
}
impl PartialEq for Logic {
    fn eq(&self, other: &Self) -> bool {
        self.0.as_ref().dyn_eq(other.0.as_ref())
    }
}
impl Eq for Logic {}
/// A point from where the Proof branches.  
/// It can either be Unprovable, have multiple viable proofs.  
/// Or it can have one valid proof.
#[derive(Debug)]
pub enum ProofBranch {
    One(Proof),
    Possible(Logic),
    Some(Vec<Proof>),
}
impl ProofBranch {
    // pub fn step<F: FnMut(&Logic, &Arc<BlockProof>) -> Vec<Proof>>(
    //     &mut self,
    //     handle: &mut F,
    //     proof: &Arc<BlockProof>,
    // ) -> Option<bool> {
    //     match self {
    //         ProofBranch::One(p) => p.step(handle),
    //         ProofBranch::Possible(logic) => {
    //             let proofs = handle(logic, proof);
    //             if proofs.is_empty() {
    //                 return Some(false);
    //             }
    //             *self = if proofs.len() == 1 {
    //                 ProofBranch::One(proofs.into_iter().next().unwrap())
    //             } else {
    //                 ProofBranch::Some(proofs)
    //             };
    //             None
    //         }
    //         ProofBranch::Some(proofs) => {
    //             let mut undecided = Vec::new();
    //             std::mem::swap(proofs, &mut undecided);
    //             for i in undecided {
    //                 match i.step(handle) {
    //                     Some(true) => {
    //                         *self = ProofBranch::One(i);
    //                         return Some(true);
    //                     }
    //                     None => proofs.push(i),
    //                     _ => {}
    //                 }
    //             }
    //             if proofs.is_empty() {
    //                 return Some(false);
    //             }
    //             if proofs.len() == 1 {
    //                 *self = ProofBranch::One(proofs.pop().unwrap());
    //             }
    //             None
    //         }
    //     }
    // }
    pub fn set_proofs(&mut self, proofs: Vec<Proof>) -> Option<bool> {
        *self = match proofs.len() {
            0 => return Some(false),
            1 => ProofBranch::One(proofs.into_iter().next().unwrap()),
            _ => ProofBranch::Some(proofs),
        };
        None
    }
    pub fn format(&self, indent: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let ProofBranch::One(proof) = self {
            proof.format(indent, f)
        } else {
            panic!()
        }
    }
    pub fn deep_clone(&self) -> Self {
        match self {
            ProofBranch::One(p) => ProofBranch::One(p.deep_clone()),
            ProofBranch::Possible(p) => ProofBranch::Possible(p.clone()),
            ProofBranch::Some(p) => ProofBranch::Some(p.iter().map(Proof::deep_clone).collect()),
        }
    }
}
#[derive(Debug)]
pub struct BlockProof {
    next_var: usize,
    assum: Logic,
    elim: Mutex<HashMap<Logic, (Vec<Proof>, bool)>>,
    root: Arc<Mutex<ProofBranch>>,
    parrent: Option<Arc<BlockProof>>,
    theorem: Logic,
}
impl BlockProof {
    pub fn new(
        assum: Logic,
        theorem: Logic,
        parrent: Arc<BlockProof>,
        branch: ProofBranch,
    ) -> Arc<BlockProof> {
        let this = Arc::new(BlockProof {
            assum,
            elim: Mutex::default(),
            next_var: parrent.next_var,
            parrent: Some(parrent.clone()),
            root: Arc::new(Mutex::new(branch)),
            theorem,
        });
        if parrent.provable(&this.assum).1 {
            return this;
        }
        {
            let mut all = this.elim.lock().unwrap();
            let mut new = vec![Proof::Assum(this.clone().assum())];
            while !new.is_empty() {
                let mut new_new = Vec::new();
                for i in new {
                    let theorem = i.theorem();
                    let entry = all.entry(theorem.clone()).or_default();
                    entry.0.push(i.clone());
                    entry.1 |= matches!(i, Proof::Assum(_));
                    let proofs = theorem.0.elim(&i, &this);
                    for i in proofs {
                        let theorem = i.theorem();
                        if !all.contains_key(&theorem) && !parrent.provable(&theorem).0 {
                            new_new.push(i);
                        }
                    }
                }
                new = new_new;
            }
        }
        this
    }
    pub fn assum(self: Arc<Self>) -> Arc<AssumProof> {
        Arc::new(AssumProof {
            theorem: self.assum.clone(),
            parrent: self,
        })
    }
    pub fn provable(&self, logic: &Logic) -> (bool, bool) {
        if let Some((proofs, by_assum)) = self.elim.lock().unwrap().get(logic) {
            if !proofs.is_empty() {
                return (true, *by_assum);
            }
        }
        self.parrent
            .as_ref()
            .map_or((false, false), |p| p.provable(logic))
    }
    pub fn proof(&self, logic: &Logic) -> Vec<Proof> {
        let mut p = self
            .elim
            .lock()
            .unwrap()
            .get(logic)
            .map_or(Vec::new(), |(p, _)| p.clone());
        if let Some(parrent) = &self.parrent {
            p.extend(parrent.proof(logic));
        }
        p
    }
}
#[derive(Debug)]
pub struct LineProof {
    dependents: Vec<Arc<Mutex<ProofBranch>>>,
    parrent: Arc<BlockProof>,
    theorem: Logic,
}
impl LineProof {
    pub fn new<const N: usize>(
        theorem: Logic,
        scope: Arc<BlockProof>,
        dependents: [ProofBranch; N],
    ) -> Arc<LineProof> {
        Arc::new(LineProof {
            dependents: dependents
                .into_iter()
                .map(Mutex::new)
                .map(Arc::new)
                .collect(),
            parrent: scope,
            theorem,
        })
    }
}
#[derive(Clone)]
pub struct AssumProof {
    parrent: Arc<BlockProof>,
    theorem: Logic,
}
impl Debug for AssumProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.theorem)
    }
}
#[derive(Clone)]
/// A proof
pub enum Proof {
    Block(Arc<BlockProof>),
    Line(Arc<LineProof>),
    Assum(Arc<AssumProof>),
    True,
}
impl Debug for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Proof::Block(p) => write!(
                f,
                "Proof(Block, {:?}, {:?}, {:?})",
                p.assum,
                p.theorem,
                &*p.root.lock().unwrap()
            ),
            Proof::Line(p) => {
                write!(f, "Proof(Line, {:?}, [", p.theorem,)?;
                for i in &p.dependents {
                    let lock = i.lock().unwrap();
                    write!(f, "{:?}, ", &*lock)?;
                }
                write!(f, "])")
            }
            Proof::Assum(p) => write!(f, "Proof(Assum, {})", p.theorem),
            Proof::True => write!(f, "Proof(True)"),
        }
    }
}
impl Proof {
    pub fn new(next_var: usize, logic: Logic) -> Proof {
        Proof::Block(Arc::new(BlockProof {
            assum: True.wrap(),
            elim: Mutex::new(HashMap::from([(True.wrap(), (vec![Proof::True], true))])),
            next_var,
            root: Arc::new(Mutex::new(ProofBranch::Possible(logic.clone()))),
            parrent: None,
            theorem: logic,
        }))
    }
    pub fn deep_clone(&self) -> Proof {
        match self {
            Proof::Block(p) => Proof::Block(Arc::new(BlockProof {
                assum: p.assum.clone(),
                elim: Mutex::new(p.elim.lock().unwrap().clone()),
                next_var: p.next_var,
                theorem: p.theorem.clone(),
                parrent: p.parrent.clone(),
                root: Arc::new(Mutex::new(p.root.lock().unwrap().deep_clone())),
            })),
            Proof::Line(p) => Proof::Line(Arc::new(LineProof {
                dependents: p
                    .dependents
                    .iter()
                    .map(|p| p.lock().unwrap().deep_clone())
                    .map(Mutex::new)
                    .map(Arc::new)
                    .collect(),
                parrent: p.parrent.clone(),
                theorem: p.theorem.clone(),
            })),
            Proof::Assum(p) => Proof::Assum(Arc::new((**p).clone())),
            Proof::True => Proof::True,
        }
    }
    pub fn parrent(&self) -> Option<&Arc<BlockProof>> {
        match self {
            Proof::Block(p) => p.parrent.as_ref(),
            Proof::Line(p) => Some(&p.parrent),
            Proof::Assum(p) => Some(&p.parrent),
            Proof::True => None,
        }
    }
    pub fn theorem(&self) -> Logic {
        match self {
            Proof::Block(p) => p.theorem.clone(),
            Proof::Line(p) => p.theorem.clone(),
            Proof::Assum(p) => p.theorem.clone(),
            Proof::True => True.wrap(),
        }
    }
    pub fn dependents(&self) -> Vec<Arc<Mutex<ProofBranch>>> {
        match self {
            Proof::Block(p) => vec![p.root.clone()],
            Proof::Line(p) => p.dependents.clone(),
            _ => vec![],
        }
    }
    // pub fn step<F: FnMut(&Logic, &Arc<BlockProof>) -> Vec<Proof>>(
    //     &self,
    //     handle: &mut F,
    // ) -> Option<bool> {
    //     let mut all = true;
    //     let parrent = match self {
    //         Proof::Block(p) => p,
    //         Proof::Line(p) => &p.parrent,
    //         Proof::Assum(p) => &p.parrent,
    //         Proof::True => todo!(),
    //     };

    //     for i in self.dependents() {
    //         let step = i.lock().unwrap().step(handle, parrent);
    //         match step {
    //             None => all = false,
    //             Some(false) => {
    //                 return Some(false);
    //             }
    //             _ => {}
    //         }
    //     }

    //     all.then_some(true)
    // }
    pub fn format(&self, indent_size: usize, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let indent = "| ".repeat(indent_size);
        match self {
            Proof::Block(p) => {
                writeln!(f, "{indent}[ {} ]", p.assum)?;
                p.root.lock().unwrap().format(indent_size + 1, f)?;
                writeln!(f, "{indent}{}", p.theorem)
            }
            Proof::Line(p) => {
                for i in &p.dependents {
                    i.lock().unwrap().format(indent_size, f)?;
                }
                writeln!(f, "{indent}{}", p.theorem)
            }
            Proof::Assum(p) => {
                writeln!(f, "{indent}{}", p.theorem)
            }
            Proof::True => writeln!(f, "{indent} {}", True),
        }
    }
    pub fn valid(&self) -> bool {
        if let Proof::Block(p) = self {
            let mut current = Some(p.clone());
            while let Some(c) = current {
                if c.elim.lock().unwrap().is_empty() {
                    if c.theorem == p.theorem {
                        return false;
                    }
                } else {
                    return true;
                }
                current = c.parrent.clone();
            }
        }
        true
    }
}
pub fn step<F: Fn(&Logic, &Arc<BlockProof>) -> Vec<Proof>>(
    this: &Proof,
    handle: &F,
) -> Option<bool> {
    let mut all = true;
    'main: for i in this.dependents() {
        let mut guard = i.lock().unwrap();
        let step = match &mut *guard {
            ProofBranch::Possible(logic) => {
                let parrent = match this {
                    Proof::Block(p) => p,
                    Proof::Line(p) => &p.parrent,
                    Proof::Assum(p) => &p.parrent,
                    Proof::True => panic!(),
                };
                let proofs = handle(logic, parrent);
                guard.set_proofs(proofs)
            }
            ProofBranch::One(p) => step(p, handle),
            ProofBranch::Some(proofs) => {
                let mut undecided = Vec::new();
                for i in proofs {
                    match step(i, handle) {
                        Some(true) => {
                            *guard = ProofBranch::One(i.clone());
                            continue 'main;
                        }
                        None => undecided.push(i.clone()),
                        _ => {}
                    }
                }
                guard.set_proofs(undecided)
            }
        };
        match step {
            None => all = false,
            Some(false) => return Some(false),
            _ => {}
        }
    }

    all.then_some(true)
}
impl Display for Proof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.format(0, f)
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct True;
impl DynLogic for True {
    fn invert(self: Arc<Self>) -> Logic {
        False.wrap()
    }
    fn intro(self: Arc<Self>, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![Proof::True]
    }
    fn elim(self: Arc<Self>, _: &Proof, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    logic_eq! {}
}
impl Display for True {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "⊤")
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
pub struct False;
impl DynLogic for False {
    fn invert(self: Arc<Self>) -> Logic {
        True.wrap()
    }
    fn intro(self: Arc<Self>, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    fn elim(self: Arc<Self>, _: &Proof, _: &Arc<BlockProof>) -> Vec<Proof> {
        vec![]
    }
    /// contridiction would give False, this gives a recursion
    fn contridict(&self) -> bool {
        false
    }
    logic_eq! {}
}
impl Display for False {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "⊥")
    }
}
