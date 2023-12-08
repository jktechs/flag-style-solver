use std::{fmt::{Display, Debug}, collections::{HashMap, HashSet, VecDeque}};
use std::hash::Hash;

#[derive(Debug, Clone)]
struct Scope {
    base: HashMap<Operator, HashSet<Line>>,
    variables: HashSet<Variable>
}
impl Scope {
    fn add_var(&mut self, mut var: Variable) -> bool {
        var.bound = false;
        self.variables.insert(var)
    }
    fn assume(&mut self, op: Operator) -> Operator {
        self.base.entry(op.clone()).or_default().insert(Line::Assume(op.clone()));
        op
    }
    fn insert(&mut self, op: Operator, line: Line) {
        if let Some(proofs) = self.base.get(&op) {
            if proofs.contains(&line) {return;}
        }
        self.base.entry(op.clone()).or_default().insert(line);
    }
    fn get(&self, op: &Operator) -> HashSet<Line> {
        self.base.get(op).cloned().unwrap_or_default()
    }
    fn expand(&mut self) {
        let mut new_scope = HashMap::<Operator, HashSet<Line>>::new();
        while self.base.len() >= 1 {
            let op = self.base.keys().next().unwrap().clone();
            for req in self.base.remove(&op).unwrap().clone() {
                match &op {
                    Operator::Conjunction(a, b) => {
                        self.insert(*a.clone(), Line::ConjElim(false,Box::new(req.clone())));
                        self.insert(*b.clone(), Line::ConjElim(true,Box::new(req.clone())));
                    },
                    Operator::Disjunction(a, b) => {
                        self.insert(*a.clone(), Line::DisjElim(Box::new(req.clone()), Err(*Operator::invert(b.clone()))));
                        self.insert(*b.clone(), Line::DisjElim(Box::new(req.clone()), Err(*Operator::invert(a.clone()))));
                    },
                    Operator::Implication(a, b) => {
                        self.insert(*b.clone(), Line::ImplElim(Box::new(req.clone()),Err(*a.clone())));
                    },
                    Operator::BiImplication(_, _) => todo!(),
                    Operator::Not(a) => {
                        self.insert(Operator::False, Line::NotElim(Box::new(req.clone()), Err(*a.clone())));
                    },
                    Operator::In(_, _) => todo!(),
                    Operator::Predicate(_, _) => {},
                    Operator::All(v, d, p) => {
                        let mut new_d = d.as_ref().clone();
                        let mut new_p = p.as_ref().clone();
                        new_d.bind(v.index, false);
                        new_p.bind(v.index, false);
                        for v2 in self.variables.clone() {
                            let mut new_d = new_d.clone();
                            let mut new_p = new_p.clone();
                            new_d.subsitute(v.index, v2.index);
                            new_p.subsitute(v.index, v2.index);
                            self.insert(new_p, Line::AllElim(Box::new(req.clone()), Err(new_d), v2));
                        }
                    },
                    Operator::Exist(v, d, p) => {
                        self.insert(Operator::False, Line::ExElim(Box::new(req.clone()),Err(Operator::All(*v, d.clone(), Operator::invert(p.clone())))));
                    },
                    Operator::Subset(_, _) => todo!(),
                    Operator::Equals(_, _) => todo!(),
                    _ => {}
                }
                new_scope.entry(op.clone()).or_default().insert(req);
            }
        }
        self.base = new_scope;
    }
}
impl Default for Scope {
    fn default() -> Self {
        Scope { base: HashMap::new(), variables: HashSet::new() }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct Variable {
    bound: bool,
    index: u32
}
impl Default for Variable {
    fn default() -> Self {
        Self { bound: false, index: u32::MAX }
    }
}
impl Variable {
    fn bound(index: u32) -> Self {
        Variable { bound: true, index }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Set {
    Variable(String),
    Intersection(Box<Set>, Box<Set>),
    Union(Box<Set>, Box<Set>),
    Difference(Box<Set>, Box<Set>),
    Def(Box<Set>, Box<Operator>),
}
#[allow(dead_code)]
#[derive(Clone, Hash, PartialEq, Eq)]
enum Operator {
    Conjunction(Box<Operator>, Box<Operator>),
    Disjunction(Box<Operator>, Box<Operator>),
    Implication(Box<Operator>, Box<Operator>),
    BiImplication(Box<Operator>, Box<Operator>),
    Not(Box<Operator>),
    In(Variable, Set),
    Predicate(String, Variable),
    Variable(String),
    All(Variable, Box<Operator>, Box<Operator>),
    Exist(Variable, Box<Operator>, Box<Operator>),
    Subset(Set, Set),
    Equals(Set, Set),
    False,
    True,
}
impl Debug for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
impl Operator {
    fn subsitute(&mut self, id_from: u32, id_to: u32) {
        match self {
            Operator::Predicate(_, v) |
            Operator::All(v, _, _) |
            Operator::Exist(v, _, _) => {if v.index == id_from {v.index = id_to}},
            Operator::Conjunction(a, b) |
            Operator::Disjunction(a, b) |
            Operator::Implication(a, b) |
            Operator::BiImplication(a, b) => {
                a.subsitute(id_from, id_to);
                b.subsitute(id_from, id_to);
            },
            Operator::Not(a) => {
                a.subsitute(id_from, id_to);
            },
            _ => {}
        }
    }
    fn bind(&mut self, id_from: u32, bl: bool) {
        match self {
            Operator::Predicate(_, v) |
            Operator::All(v, _, _) |
            Operator::Exist(v, _, _) => {if v.index == id_from {v.bound = bl}},
            Operator::Conjunction(a, b) |
            Operator::Disjunction(a, b) |
            Operator::Implication(a, b) |
            Operator::BiImplication(a, b) => {
                a.bind(id_from, bl);
                b.bind(id_from, bl);
            },
            Operator::Not(a) => {
                a.bind(id_from, bl);
            },
            _ => {}
        }
    }
    fn invert(mut op: Box<Self>) -> Box<Self> {
        match *op {
            Operator::Not(a) => a,
            Operator::All(v, d, p) => Box::new(Operator::Exist(v, d, Self::invert(p))),
            Operator::Exist(v, d, p) => Box::new(Operator::All(v, d, Self::invert(p))),
            Operator::False => {*op = Operator::True; op},
            Operator::True => {*op = Operator::False; op},
            _ => {Box::new(Operator::Not(op))}
        }
    }
}
#[allow(dead_code)]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Line {
    Assume(Operator),

    ConjElim(bool, Box<Line>),
    BiImplElim(bool, Box<Line>),

    ConjIntro(Box<Line>, Box<Line>),
    BiImplInto(Box<Line>, Box<Line>),
    DisjElim(Box<Line>, Result<Box<Line>, Operator>),
    ExElim(Box<Line>, Result<Box<Line>, Operator>),
    ImplElim(Box<Line>, Result<Box<Line>, Operator>),
    AllElim(Box<Line>, Result<Box<Line>, Operator>, Variable),
    NotElim(Box<Line>, Result<Box<Line>, Operator>),

    DisjIntro(Box<Line>, Operator),
    ImplIntro(Box<Line>, Operator),
    AllIntro(Box<Line>, Variable, Operator),
    ExIntro(Box<Line>, Variable, Operator),
    NotIntro(Box<Line>, Operator),
    FalseElim(Box<Line>, Operator)
}
// (Vx[x in N:P(x)]=>Ey[y in N:Q(y)]) => Ez[z in N: P(z) => Q(z)]
fn main() {
    let root = Operator::Implication(Box::new(Operator::Implication(Box::new(Operator::All(Variable::bound(0), Box::new(Operator::Predicate("N".into(), Variable::bound(0))), Box::new(Operator::Predicate("P".into(), Variable::bound(0))))), Box::new(Operator::Exist(Variable::bound(1), Box::new(Operator::Predicate("N".into(), Variable::bound(1))), Box::new(Operator::Predicate("Q".into(), Variable::bound(1))))))), Box::new(Operator::Exist(Variable::bound(2), Box::new(Operator::Predicate("N".into(), Variable::bound(2))), Box::new(Operator::Implication(Box::new(Operator::Predicate("P".into(), Variable::bound(2))),Box::new(Operator::Predicate("Q".into(), Variable::bound(2))))) )));
    //let root = Operator::Implication(Box::new(Operator::Conjunction(Box::new(Operator::Conjunction(Box::new(Operator::Implication(Box::new(Operator::Variable("P".into())), Box::new(Operator::Variable("Z".into())))), Box::new(Operator::Implication(Box::new(Operator::Variable("Q".into())), Box::new(Operator::Variable("Z".into())))))), Box::new(Operator::Disjunction(Box::new(Operator::Variable("P".into())), Box::new(Operator::Variable("Q".into())))))), Box::new(Operator::Variable("Z".into())));
    println!("{}", root);
    println!("{}", prove(root, Scope::default(), 0).unwrap().render());
}
fn prove(end: Operator, mut scope: Scope, n: usize) -> Result<Line, ()> {
    println!("{}",n);
    //println!("{}Proving: {}", " ".repeat(n), end);
    if let Ok(line) = try_short_circuit(&end, scope.clone(), n + 1) {return Ok(line)}
    scope.expand();
    if let Ok(line) = try_still_valid(&end, &scope, n + 1) {return Ok(line)}
    if let Ok(line) = try_still_valid(&Operator::False, &scope, n + 1) {return Ok(Line::FalseElim(Box::new(line), end))}
    if let Ok(line) = try_raa(&end, scope.clone(), n + 1) {return Ok(line)}

    Err(())
}
fn try_raa<'a>(end: &Operator, mut scope: Scope, n: usize) -> Result<Line, ()> {
    if end == &Operator::False {return Err(())}
    let inv = *Operator::invert(Box::new(end.clone()));
    scope.assume(inv.clone());
    // println!("{}doing raa on {}", " ".repeat(n), end);
    match prove(Operator::False, scope, n) {
        Ok(proof) => {
            return Ok(Line::NotIntro(Box::new(proof), inv.clone()));
        },
        Err(_) => {Err(())},
    }
}
fn try_still_valid(end: &Operator, scope: &Scope, n: usize) -> Result<Line, ()> {
    let mut n_off = 0;
    let proofs = scope.get(end);
    if proofs.len() != 0 {
        'proof_loop:
        for mut proof in proofs {
            n_off = 0;
            //println!("{}found it via {}", " ".repeat(n), proof.get_hint());
            for missing in get_missing(&mut proof) {
                if let Err(end) = missing {
                    match prove(end.clone(), scope.clone(), n + n_off) {
                        Ok(new_line) => {
                            *missing = Ok(Box::new(new_line))
                        },
                        Err(_) => continue 'proof_loop,
                    }
                    n_off += 1;
                }
            }
            return Ok(proof)
        }
    }
    Err(())
}
fn try_short_circuit(end: &Operator, mut scope: Scope, n: usize) -> Result<Line, ()> {
    match end.clone() {
        Operator::Implication(a, b) => {
            // println!("{}shortcut impl", " ".repeat(n));
            let asum = scope.assume(*a);
            let proof = prove(*b, scope, n)?;
            Ok(Line::ImplIntro(Box::new(proof), asum))
        },
        Operator::Not(a) => {
            // println!("{}shortcut not", " ".repeat(n));
            let asum = scope.assume(*a);
            let proof = prove(Operator::False, scope, n)?;
            Ok(Line::NotIntro(Box::new(proof), asum))
        },
        Operator::All(var, mut domain, mut predicate) => {
            // println!("{}shortcut for all", " ".repeat(n));
            domain.bind(var.index, false);
            predicate.bind(var.index, false);
            let asum = scope.assume(*domain);
            scope.add_var(var);
            let proof = prove(*predicate, scope, n)?;
            Ok(Line::AllIntro(Box::new(proof), var, asum))
        },
        Operator::Exist(var, domain, predicate) => {
            // println!("{}shortcut exists", " ".repeat(n));
            let asum = scope.assume(Operator::All(var, domain, Operator::invert(predicate)));
            let proof = prove(Operator::False, scope, n)?;
            Ok(Line::ExIntro(Box::new(proof), var, asum))
        },
        Operator::True => Ok(Line::Assume(Operator::True)),

        Operator::In(_, _) => todo!(),
        Operator::Subset(_, _) => todo!(),
        Operator::Equals(_, _) => todo!(),

        Operator::BiImplication(_, _) => todo!(),
        Operator::Conjunction(_, _) => todo!(),
        Operator::Disjunction(_, _) => todo!(),

        Operator::False |
        Operator::Variable(_) |
        Operator::Predicate(_, _) => Err(())
    }
}
fn get_missing(line: &mut Line) -> Vec<&mut Result<Box<Line>, Operator>> {
    let mut v = Vec::new();
    match line {
        Line::AllElim(a, b, _) |
        Line::DisjElim(a, b) |
        Line::ExElim(a, b) |
        Line::ImplElim(a, b) |
        Line::NotElim(a, b) => {
            v.append(&mut get_missing(a.as_mut()));
            v.push(b);
        }
        Line::ConjIntro(a, b) |
        Line::BiImplInto(a, b) => {
            v.append(&mut get_missing(a.as_mut()));
            v.append(&mut get_missing(b.as_mut()));
        },
        Line::ConjElim(_, a) |
        Line::BiImplElim(_, a) |
        Line::DisjIntro(a, ..) |
        Line::ImplIntro(a, ..) |
        Line::AllIntro(a, ..) |
        Line::ExIntro(a, ..) |
        Line::FalseElim(a, _) |
        Line::NotIntro(a, ..) => v.append(&mut get_missing(a.as_mut())),
        _ => {},
    }
    v
}


impl Display for Set {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Set::Variable(name) => write!(f, "{}", name),
            Set::Def(domain, predicate) => write!(f, "{{{}|{}}}", domain, predicate),
            Set::Intersection(a, b) => write!(f, "{}n{}", a, b),
            Set::Union(a, b) => write!(f, "{}u{}", a, b),
            Set::Difference(a, b) => write!(f, "{}\\{}", a, b),
        }
    }
}
impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operator::Not(a) => write!(f, "!({})", a),
            Operator::In(id, set) => write!(f, "({} in {})", id, set),
            Operator::Predicate(name, param) => write!(f, "{}({})", name, param),
            Operator::Variable(name) => write!(f, "{}", name),
            Operator::Subset(a, b) => write!(f, "({}C={})", a, b),
            Operator::Equals(a, b) => write!(f, "({}={})", a, b),
            Operator::False => write!(f, "False"),
            Operator::True => write!(f, "True"),
            Operator::Conjunction(a, b) => write!(f, "({}/\\{})", a, b),
            Operator::Disjunction(a, b) => write!(f, "({}\\/{})", a, b),
            Operator::Implication(a, b) => write!(f, "({}=>{})", a, b),
            Operator::BiImplication(a, b) => write!(f, "({}<=>{})", a, b),
            Operator::All(v, d, p) => write!(f, "V{}[{}:{}]", v, d, p),
            Operator::Exist(v, d, p) => write!(f, "E{}[{}:{}]", v, d, p),
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
#[derive(Debug)]
enum Statement {
    Block {
        hint: String,
        assumption: Operator,
        inside: Box<Statement>,
        label: Operator
    },
    Line {
        previous: Vec<Box<Statement>>,
        hint: String,
        label: Operator
    },
    StillValid {
        assumption: Operator
    }
}
impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Block { hint, assumption, inside, label } => {
                writeln!(f, "{{Assume:}}")?;
                writeln!(f, "[ {} ]", assumption)?;
                let mut inside = format!("{}", inside).replace("\n", "\n|");
                inside.pop();
                write!(f, "|{}", inside)?;
                writeln!(f, "{{{}:}}", hint)?;
                writeln!(f, "{}", label)
            },
            Statement::Line { previous, hint, label } => {
                for s in previous {
                    write!(f, "{}", s)?;
                }
                writeln!(f, "{{{}:}}", hint)?;
                writeln!(f, "{}", label)
            },
            Statement::StillValid { assumption } => {
                writeln!(f, "{{Still valid:}}")?;
                writeln!(f, "{}", assumption)
            },
        }
    }
}
impl Line {
    fn render(&self) -> Statement {
        let hint: String = self.get_hint().into();
        let vls = match self {
            Line::Assume(a) => return Statement::StillValid { assumption: a.clone() },

            Line::ConjElim(_, a) |
            Line::BiImplElim(_, a) |
            Line::FalseElim(a, _) => Ok(vec![a.render()]),

            Line::ConjIntro(a, b) |
            Line::BiImplInto(a, b) => Ok(vec![a.render(), b.render()]),

            Line::DisjElim(a, b) |
            Line::AllElim(a, b, _) |
            Line::NotElim(a, b) |
            Line::ExElim(a, b) |
            Line::ImplElim(a, b) => Ok(vec![a.render(), b.as_ref().unwrap().render()]),
            
            Line::DisjIntro(a, b) |
            Line::AllIntro(a, _, b) |
            Line::NotIntro(a, b) |
            Line::ImplIntro(a, b) |
            Line::ExIntro(a, _, b) => Err((a.render(), b.clone())),
        };
        let label = *self.get_label();
        match vls {
            Ok(elms) => {
                Statement::Line { previous: elms.into_iter().map(Box::new).collect(), hint, label }
            },
            Err((elm, assumption)) => {
                Statement::Block { hint, assumption, inside: Box::new(elm), label }
            }
        }
    }
    fn get_hint(&self) -> &'static str {
        match self {
            Line::Assume(_) => "Assume",
            Line::ConjElim(_, _) => "/\\ - Elim",
            Line::BiImplElim(_, _) => "<=> - Elim",
            Line::DisjElim(_, _) => "\\/ - Elim",
            Line::ConjIntro(_, _) => "/\\ - Intro",
            Line::BiImplInto(_, _) => "<=> - Into",
            Line::ExElim(_, _) => "E - Elim",
            Line::ImplElim(_, _) => "=> - Elim",
            Line::AllElim(_, _, _) => "A - Elim",
            Line::NotElim(_, _) => "! - Elim",
            Line::DisjIntro(_, _) => "\\/ - Intro",
            Line::ImplIntro(_, _) => "=> - Intro",
            Line::AllIntro(_, _, _) => "A - Intro",
            Line::ExIntro(_, _, _) => "E - Intro",
            Line::NotIntro(_, _) => "! - Intro",
            Line::FalseElim(_, _) => "False - Elim",
        }
    }
    fn get_label(&self) -> Box<Operator> {
        match self {
            Line::Assume(a) => Box::new(a.clone()),
            Line::ConjElim(a, b) => {
                if let Operator::Conjunction(a2, b2) = *b.get_label() {
                    if *a {
                        b2
                    } else {
                        a2
                    }
                } else {panic!()}
            },
            Line::BiImplElim(_, _) => todo!(),
            Line::DisjElim(a, b) => {
                if let Operator::Disjunction(a2, b2) = *a.get_label() {
                    if b.as_ref().unwrap().get_label() == a2 {
                        b2
                    } else {
                        a2
                    }
                } else {panic!()}
            },
            Line::ConjIntro(_, _) => todo!(),
            Line::BiImplInto(_, _) => todo!(),
            Line::ExElim(_, _) => Box::new(Operator::False),
            Line::ImplElim(imp, _) => {
                if let Operator::Implication(_, b) = *imp.get_label() {
                    b
                } else {panic!()}
            },
            Line::AllElim(all, _, var) => {
                if let Operator::All(v, _, mut pr) = *all.get_label() {
                    pr.subsitute(v.index, var.index);
                    pr
                } else {panic!()}
            },
            Line::NotElim(_, _) => Box::new(Operator::False),
            Line::DisjIntro(_, _) => todo!(),
            Line::ImplIntro(a, b) => Box::new(Operator::Implication(Box::new(b.clone()), a.get_label())),
            Line::AllIntro(a, b, c) => Box::new(Operator::All(b.clone(), Box::new(c.clone()), a.get_label())),
            Line::ExIntro(_, b, c) => {
                if let Operator::All(_, b2, c2) = c {
                    Box::new(Operator::Exist(b.clone(), b2.clone(), Operator::invert(c2.clone())))
                } else {panic!()}
            },
            Line::NotIntro(_, b) => {
                Operator::invert(Box::new(b.clone()))
            },
            Line::FalseElim(_, a) => Box::new(a.clone()),
        }
    }
}