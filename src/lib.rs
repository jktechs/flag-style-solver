use std::{fmt::{Debug, Display}, collections::{HashSet, HashMap}};

#[derive(Debug, Clone, Hash, PartialEq, Eq, Copy)]
pub struct Variable {
    pub bound: bool,
    pub index: u32
}
// #[derive(Debug, Clone, Hash, PartialEq, Eq)]
// enum Set {
//     Empty,
//     Variable(String),
//     Intersection(Box<Set>, Box<Set>),
//     Union(Box<Set>, Box<Set>),
//     Difference(Box<Set>, Box<Set>),
//     Def(Box<Set>, Box<Predicate>),
// }
#[allow(dead_code)]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Predicate {
    Conjunction(Box<Predicate>, Box<Predicate>),
    Disjunction(Box<Predicate>, Box<Predicate>),
    Implication(Box<Predicate>, Box<Predicate>),
    BiImplication(Box<Predicate>, Box<Predicate>),
    Not(Box<Predicate>),
    PredicateVariable(String, Variable),
    Variable(String),
    All(Variable, Box<Predicate>, Box<Predicate>),
    Exist(Variable, Box<Predicate>, Box<Predicate>),
    False,
    True,
    // Subset(Set, Set),
    // Equals(Set, Set),
    // In(Variable, Set),
}
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Line {
    True,
    Proof(Result<Box<Line>, Predicate>),
    Assume(Predicate),

    ConjElim(bool, Box<Line>), // side: F-T, conjuntion
    BiImplElim(bool, Box<Line>), // side F-T, biimplication

    DisjElim(Box<Line>, Result<Box<Line>, Predicate>), // disjunection, proof inversion of one
    ExElim(Box<Line>, Result<Box<Line>, Predicate>), // existance, for all
    ImplElim(Box<Line>, Result<Box<Line>, Predicate>), // implication, proof assumption
    AllElim(Box<Line>, Result<Box<Line>, Predicate>, Variable), // for all, proof domain, variable to subsitute
    NotElim(Box<Line>, Result<Box<Line>, Predicate>), // inversion, proof contridiction

    ConjIntro(Result<Box<Line>, Predicate>, Result<Box<Line>, Predicate>), // proof left, proof right
    BiImplInto(Result<Box<Line>, Predicate>, Result<Box<Line>, Predicate>), // proof left impl right, proof right impl left
    DisjIntro(Result<Box<Line>, Predicate>, Predicate, bool), // proof one without other, assumption
    ImplIntro(Result<Box<Line>, Predicate>, Predicate), // proof, assumption
    AllIntro(Result<Box<Line>, Predicate>, Predicate, Variable), // proof, domain assumption, variable
    ExIntro(Result<Box<Line>, Predicate>, Predicate), // proof contridiction, assumption, variable
    NotIntro(Result<Box<Line>, Predicate>, Predicate), // proof contridiction, assumption
    FalseElim(Box<Line>, Predicate) // proof contridiction, result
}
impl Predicate {
    pub fn subsitute(&mut self, id_from: u32, id_to: u32) {
        use Predicate::*;
        match self {
            PredicateVariable(_, v) |
            All(v, _, _) |
            Exist(v, _, _) => {if v.index == id_from {v.index = id_to; v.bound = false}},
            Conjunction(a, b) |
            Disjunction(a, b) |
            Implication(a, b) |
            BiImplication(a, b) => {
                a.subsitute(id_from, id_to);
                b.subsitute(id_from, id_to);
            },
            Not(a) => {
                a.subsitute(id_from, id_to);
            },
            _ => {}
        }
    }
    pub fn invert(mut op: Box<Self>) -> Box<Self> {
        use Predicate::*;
        match *op {
            Not(a) => a,
            All(v, d, p) => Box::new(Exist(v, d, Self::invert(p))),
            Exist(v, d, p) => Box::new(All(v, d, Self::invert(p))),
            False => {*op = True; op},
            True => {*op = False; op},
            _ => {Box::new(Not(op))}
        }
    }
    pub fn intro(&self) -> Vec<Line> {
        use Predicate::*;
        match self.clone() {
            Implication(a, b) => vec![Line::ImplIntro(Err(*b), *a)],
            Not(a) => vec![Line::NotIntro(Err(Predicate::False), *a)],
            All(var, domain, predicate) => vec![Line::AllIntro(Err(*predicate), *domain, var)],
            Exist(var, domain, predicate) => vec![Line::ExIntro(Err(Predicate::False), All(var, domain, Predicate::invert(predicate)))],
            BiImplication(a, b) => vec![Line::BiImplInto(Err(Implication(a.clone(), b.clone())), Err(Implication(b, a)))],
            Conjunction(a, b) => vec![Line::ConjIntro(Err(*a), Err(*b))],
            Disjunction(a, b) => vec![Line::DisjIntro(Err(*a.clone()), *Predicate::invert(b.clone()), false), Line::DisjIntro(Err(*b), *Predicate::invert(a), true)],
            False | Variable(_) | PredicateVariable(_, _) => vec![],
            True => vec![Line::True],
            // In(_, _) => todo!(),
            // Subset(_, _) => todo!(),
            // Equals(_, _) => todo!(),
        }
    }
}
impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { // ∅
        match self {
            Predicate::Conjunction(a, b) => write!(f, "({}∧{})", a, b),
            Predicate::Disjunction(a, b) => write!(f, "({}∨{})", a, b),
            Predicate::Implication(a, b) => write!(f, "({}⇒{})", a, b),
            Predicate::BiImplication(a, b) => write!(f, "({}⇔{})", a, b),
            Predicate::Not(a) => write!(f, "¬{}", a),
            Predicate::PredicateVariable(a, b) => write!(f, "{}({})", a, b),
            Predicate::Variable(a) => write!(f, "{}", a),
            Predicate::All(a, b, c) => write!(f, "∀{}[{}: {}]", a, b, c),
            Predicate::Exist(a, b, c) => write!(f, "∃{}[{}: {}]", a, b, c),
            Predicate::False => write!(f, "False"),
            Predicate::True => write!(f, "True"),
        }
    }
}
impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.index {
            0 => write!(f, "x"),
            1 => write!(f, "y"),
            2 => write!(f, "z"),
            _ => write!(f, "{}", self.index)
        }
    }
}
impl Display for Line {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Line::True => write!(f, "True"),
            Line::Proof(a) => write!(f, "{}", a.as_ref().unwrap()),
            Line::Assume(_) => {Ok(())},
            Line::ConjElim(_, a) |
            Line::FalseElim(a, _) |
            Line::BiImplElim(_, a) => {
                write!(f, "{}", a)?;
                writeln!(f, "{}", self.hint())?;
                writeln!(f, "{}", self.label())
            }

            Line::ConjIntro(Ok(a), Ok(b)) |
            Line::BiImplInto(Ok(a), Ok(b)) |
            Line::AllElim(a, Ok(b), _) |
            Line::DisjElim(a, Ok(b)) |
            Line::ExElim(a, Ok(b)) |
            Line::ImplElim(a, Ok(b)) |
            Line::NotElim(a, Ok(b)) => {
                write!(f, "{}", a)?;
                write!(f, "{}", b)?;
                writeln!(f, "{{{}:}}", self.hint())?;
                writeln!(f, "{}", self.label())
            },

            Line::DisjIntro(Ok(a), b, _) |
            Line::ImplIntro(Ok(a), b) |
            Line::AllIntro(Ok(a), b, _) |
            Line::ExIntro(Ok(a), b) |
            Line::NotIntro(Ok(a), b) => {
                writeln!(f, "{{Assume:}}")?;
                writeln!(f, "[ {} ]", b)?;
                let s = a.to_string();
                let p = s.lines().collect::<Vec<_>>();
                write!(f, "|{}\n", p.join("\n|"))?;
                writeln!(f, "{{{}:}}", self.hint())?;
                writeln!(f, "{}", self.label())
            }
            _ => panic!()
        }
    }
}
impl Line {
    pub fn hint(&self) -> String {
        match self {
            Line::True => "Always valid".to_string(),
            Line::Proof(_) => panic!(),
            Line::Assume(_) => panic!(),
            Line::ConjElim(_, _) => "∧ - elim".to_string(),
            Line::BiImplElim(_, _) => "⇔ - elim".to_string(),
            Line::DisjElim(_, _) => "∨ - elim".to_string(),
            Line::ExElim(_, _) => "∃ - elim".to_string(),
            Line::ImplElim(_, _) => "⇒ - elim".to_string(),
            Line::AllElim(_, _, _) => "∀ - elim".to_string(),
            Line::NotElim(_, _) => "¬ - elim".to_string(),
            Line::ConjIntro(_, _) => "∧ - intro".to_string(),
            Line::BiImplInto(_, _) => "⇔ - intro".to_string(),
            Line::DisjIntro(_, _, _) => "∨ - intro".to_string(),
            Line::ImplIntro(_, _) => "⇒ - intro".to_string(),
            Line::AllIntro(_, _, _) => "∀ - intro".to_string(),
            Line::ExIntro(_, _) => "∃ - intro".to_string(),
            Line::NotIntro(_, _) => "¬ - intro".to_string(),
            Line::FalseElim(_, _) => "false - elim".to_string(),
        }
    }
    pub fn try_label(result: &Result<Box<Line>, Predicate>) -> Predicate {
        match result {
            Ok(a) => a.label(),
            Err(a) => a.clone(),
        }
    }
    pub fn label(&self) -> Predicate {
        match self {
            Line::Assume(a) => a.clone(),

            Line::ConjElim(a, b) => {
                if let Predicate::Conjunction(a2, b2) = b.label() {
                    if *a {
                        *b2
                    } else {
                        *a2
                    }
                } else {panic!()}
            },
            Line::DisjElim(a, b) => {
                if let Predicate::Disjunction(a2, b2) = a.label() {
                    if Line::try_label(b) == *Predicate::invert(a2.clone()) {
                        *b2
                    } else {
                        *a2
                    }
                } else {panic!()}
            },
            Line::BiImplElim(a, b) => {
                if let Predicate::BiImplication(a2, b2) = b.label() {
                    if *a {
                        Predicate::Implication(a2, b2)
                    } else {
                        Predicate::Implication(b2, a2)
                    }
                } else {panic!()}
            },
            Line::ImplElim(imp, _) => {
                if let Predicate::Implication(_, b) = imp.label() {
                    *b
                } else {panic!()}
            },
            Line::AllElim(all, _, var) => {
                if let Predicate::All(v, _, mut pr) = all.label() {
                    pr.subsitute(v.index, var.index);
                    *pr
                } else {panic!()}
            },
            Line::NotElim(_, _) |
            Line::ExElim(_, _) => Predicate::False,

            Line::ConjIntro(a, b) => Predicate::Conjunction(Box::new(Line::try_label(a)), Box::new(Line::try_label(b))),
            Line::BiImplInto(a, _) => {
                if let Predicate::Implication(a2, b2) = Line::try_label(a) {
                    Predicate::BiImplication(a2, b2)
                } else {panic!()}
            },
            Line::DisjIntro(a, b, c) => {
                if *c {
                    Predicate::Disjunction(Predicate::invert(Box::new(b.clone())), Box::new(Line::try_label(a)))
                } else {
                    Predicate::Disjunction(Box::new(Line::try_label(a)), Predicate::invert(Box::new(b.clone())))
                }
            },
            Line::ImplIntro(a, b) => Predicate::Implication(Box::new(b.clone()), Box::new(Line::try_label(a))),
            Line::AllIntro(a, b, c) => Predicate::All(c.clone(), Box::new(b.clone()), Box::new(Line::try_label(a))),
            Line::ExIntro(_, c) => {
                if let Predicate::All(v, b2, c2) = c {
                    Predicate::Exist(v.clone(), b2.clone(), Predicate::invert(c2.clone()))
                } else {panic!()}
            },
            Line::NotIntro(_, b) => *Predicate::invert(Box::new(b.clone())),
            Line::FalseElim(_, a) => a.clone(),
            Line::True => Predicate::True,
            Line::Proof(a) => Line::try_label(a),
        }
    }
    pub fn elim(&self, vs: &HashSet<Variable>) -> Vec<Line> {
        use Predicate::*;
        match self.label() {
            Conjunction(_, _) => vec![Line::ConjElim(false, Box::new(self.clone())), Line::ConjElim(true, Box::new(self.clone()))],
            Disjunction(a, b) => vec![Line::DisjElim(Box::new(self.clone()), Err(*Predicate::invert(a.clone()))), Line::DisjElim(Box::new(self.clone()), Err(*Predicate::invert(b.clone())))],
            Implication(a, _) => vec![Line::ImplElim(Box::new(self.clone()), Err(*a.clone()))],
            BiImplication(_, _) => vec![Line::BiImplElim(false, Box::new(self.clone())), Line::BiImplElim(true, Box::new(self.clone()))],
            Exist(v, d, p) => vec![Line::ExElim(Box::new(self.clone()), Err(All(v, d, Predicate::invert(p))))],
            Not(a) => vec![Line::NotElim(Box::new(self.clone()), Err(*a))],
            PredicateVariable(_, _) | Variable(_) | False | True => vec![],
            All(v, d, _) => {
                vs.into_iter().map(|v2| {
                    let mut new_d = d.as_ref().clone();
                    new_d.subsitute(v.index, v2.index);
                    Line::AllElim(Box::new(self.clone()), Err(new_d), v2.clone())
                }).collect()
            },
            // Subset(_, _) => todo!(),
            // Equals(_, _) => todo!(),
            // In(_, _) => todo!(),
        }
    }
    pub fn next(&mut self) -> Option<(&mut Result<Box<Line>, Predicate>, HashSet<Variable>, HashSet<Predicate>)> {
        match self {
            Line::FalseElim(a, _) |
            Line::BiImplElim(_, a) |
            Line::ConjElim(_, a) => a.next(),
            Line::Assume(_) |
            Line::True => None,
            Line::ImplElim(_, a) |
            Line::DisjElim(_, a) |
            Line::NotElim(_, a) |
            Line::AllElim(_, a, _) |
            Line::ExElim(_, a) |
            Line::Proof(a) => {
                if a.is_err() {
                    Some((a, HashSet::new(), HashSet::new()))
                } else {
                    a.as_mut().unwrap().next()
                }
            },
            Line::ConjIntro(a, b) |
            Line::BiImplInto(a, b) => {
                if a.is_err() {
                    Some((a, HashSet::new(), HashSet::new()))
                } else if b.is_err() {
                    Some((b, HashSet::new(), HashSet::new()))
                } else {
                    a.as_mut().unwrap().next().or_else(|| b.as_mut().unwrap().next())
                }
            },
            Line::DisjIntro(a, b, _) |
            Line::ImplIntro(a, b) |
            Line::ExIntro(a, b) |
            Line::NotIntro(a, b) => {
                if a.is_err() {
                    Some((a, HashSet::new(), vec![b.clone()].into_iter().collect()))
                } else {
                    let mut next = a.as_mut().unwrap().next();
                    if let Some((_,_,x)) = next.as_mut() {
                        x.insert(b.clone());
                    }
                    next
                }
            },
            Line::AllIntro(a, b, c) => {
                if a.is_err() {
                    Some((a, vec![c.clone()].into_iter().collect(), vec![b.clone()].into_iter().collect()))
                } else {
                    let mut next = a.as_mut().unwrap().next();
                    if let Some((_,y,x)) = next.as_mut() {
                        x.insert(b.clone());
                        y.insert(c.clone());
                    }
                    next
                }
            }
        }
    }
}
pub fn prove(formula: Predicate) -> Line {
    let mut trees = HashSet::new();
    trees.insert(Line::Proof(Err(formula)));
    for _ in 0..5 {
        let mut to_add = HashSet::new();
        println!("---------------------------");
        for i in trees.iter() {
            println!("{:?}", i);
        }
        for tree in trees.iter() {
            let mut tmp = tree.clone();
            if let Some((elm, vars, asums)) = tmp.next() {
                let to_prove = elm.as_mut().err().unwrap();
                let mut asums = asums.into_iter().map(|x| Line::Assume(x)).collect::<HashSet<_>>();
                let mut new_assums = HashSet::new();
                while let Some(line) = asums.iter().next() {
                    let line = line.clone();
                    asums.remove(&line);
                    asums.extend(line.elim(&vars).into_iter());
                    new_assums.insert(line);
                }
                let mut asums = HashMap::<Predicate, HashSet<Line>>::new();
                for line in new_assums {
                    asums.entry(line.label()).or_default().insert(line);
                }
                let mut proofs = to_prove.intro(); // Bottom-up
                proofs.extend(asums.remove(to_prove).unwrap_or_default().into_iter()); // Top-down
                proofs.extend(asums.remove(&Predicate::False).unwrap_or_default().into_iter().map(|x| Line::FalseElim(Box::new(x), to_prove.clone()))); // False elim
                proofs.push(Line::NotIntro(Err(Predicate::False), *Predicate::invert(Box::new(to_prove.clone())))); // RAA
                for line in proofs {
                    let mut new_tmp = tree.clone();
                    *new_tmp.next().unwrap().0 = Ok(Box::new(line));
                    to_add.insert(new_tmp);
                }
            } else {
                return tmp;
            }
        }
        trees = to_add;
    }
    panic!()
}