use std::{fmt::{Display, Debug}, collections::{HashMap, HashSet, VecDeque}};
use std::hash::Hash;

#[derive(Debug, Clone)]
struct Scope<'a> {
    base: HashMap<Operator<'a>, HashSet<Line<'a>>>,
    variables: HashSet<Variable>,
    proof_chain: VecDeque<Operator<'a>>
}
impl<'a> Scope<'a> {
    fn add_var(&mut self, mut var: Variable) -> bool {
        var.bound = false;
        self.variables.insert(var)
    }
    fn assume(&mut self, op: Operator<'a>) -> Operator<'a> {
        self.base.entry(op.clone()).or_default().insert(Line::Assume(op.clone()));
        op
    }
    fn insert(&mut self, op: Operator<'a>, line: Line<'a>) {
        if let Some(proofs) = self.base.get(&op) {
            if proofs.contains(&line) {return;}
        }
        self.base.entry(op.clone()).or_default().insert(line);
    }
    fn get(&self, op: &Operator<'a>) -> HashSet<Line<'a>> {
        self.base.get(op).cloned().unwrap_or_default()
    }
    fn chain(&mut self, op: &Operator<'a>) {
        if let Operator::False = op {return;}
        self.proof_chain.push_back(op.clone());
    }
    fn expand(&mut self) {
        let mut new_scope = HashMap::<Operator<'a>, HashSet<Line<'a>>>::new();
        while self.base.len() >= 1 {
            let op = self.base.keys().next().unwrap().clone();
            for req in self.base.remove(&op).unwrap().clone() {
                match &op {
                    Operator::Conjunction(_, _) => todo!(),
                    Operator::Disjunction(_, _) => todo!(),
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
impl<'a> Default for Scope<'a> {
    fn default() -> Self {
        Scope { base: HashMap::new(), variables: HashSet::new(), proof_chain: VecDeque::new() }
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
enum Set<'a> {
    Variable(&'a str),
    Intersection(Box<Set<'a>>, Box<Set<'a>>),
    Union(Box<Set<'a>>, Box<Set<'a>>),
    Difference(Box<Set<'a>>, Box<Set<'a>>),
    Def(Box<Set<'a>>, Box<Operator<'a>>),
}
#[allow(dead_code)]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum Operator<'a> {
    Conjunction(Box<Operator<'a>>, Box<Operator<'a>>),
    Disjunction(Box<Operator<'a>>, Box<Operator<'a>>),
    Implication(Box<Operator<'a>>, Box<Operator<'a>>),
    BiImplication(Box<Operator<'a>>, Box<Operator<'a>>),
    Not(Box<Operator<'a>>),
    In(Variable, Set<'a>),
    Predicate(&'a str, Variable),
    Variable(&'a str),
    All(Variable, Box<Operator<'a>>, Box<Operator<'a>>),
    Exist(Variable, Box<Operator<'a>>, Box<Operator<'a>>),
    Subset(Set<'a>, Set<'a>),
    Equals(Set<'a>, Set<'a>),
    False,
    True,
}
impl<'a> Operator<'a> {
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
enum Line<'a> {
    Assume(Operator<'a>),

    ConjElim(bool, Box<Line<'a>>),
    BiImplElim(bool, Box<Line<'a>>),

    DisjElim(Box<Line<'a>>, Box<Line<'a>>),
    ConjIntro(Box<Line<'a>>, Box<Line<'a>>),
    BiImplInto(Box<Line<'a>>, Box<Line<'a>>),
    ExElim(Box<Line<'a>>, Result<Box<Line<'a>>, Operator<'a>>),
    ImplElim(Box<Line<'a>>, Result<Box<Line<'a>>, Operator<'a>>),
    AllElim(Box<Line<'a>>, Result<Box<Line<'a>>, Operator<'a>>, Variable),
    NotElim(Box<Line<'a>>, Result<Box<Line<'a>>, Operator<'a>>),

    DisjIntro(Box<Line<'a>>, Operator<'a>),
    ImplIntro(Box<Line<'a>>, Operator<'a>),
    AllIntro(Box<Line<'a>>, Variable, Operator<'a>),
    ExIntro(Box<Line<'a>>, Variable, Operator<'a>),
    NotIntro(Box<Line<'a>>, Operator<'a>),
    FalseElim(Box<Line<'a>>, Operator<'a>)
}
// (Vx[x in N:P(x)]=>Ey[y in N:Q(y)]) => Ez[z in N: P(z) => Q(z)]
fn main() {
    let root = Operator::Implication(Box::new(Operator::Implication(Box::new(Operator::All(Variable::bound(0), Box::new(Operator::Predicate("N", Variable::bound(0))), Box::new(Operator::Predicate("P", Variable::bound(0))))), Box::new(Operator::Exist(Variable::bound(1), Box::new(Operator::Predicate("N", Variable::bound(1))), Box::new(Operator::Predicate("Q", Variable::bound(1))))))), Box::new(Operator::Exist(Variable::bound(2), Box::new(Operator::Predicate("N", Variable::bound(2))), Box::new(Operator::Implication(Box::new(Operator::Predicate("P", Variable::bound(2))),Box::new(Operator::Predicate("Q", Variable::bound(2))))) )));
    println!("{}", root);
    println!("{}", prove(root, Scope::default(), 0).unwrap().render().unwrap());
}
fn prove<'a>(end: Operator<'a>, mut scope: Scope<'a>, mut n: usize) -> Result<Line<'a>, ()> {
    n += 1;
    let reqursion = scope.proof_chain.iter().any(|x| &end == x);

    //println!("{}Proving: {}", " ".repeat(n), end);
    scope.chain(&end);
    if !reqursion {
        if let Ok(line) = try_short_circuit(&end, scope.clone(), n) {return Ok(line)}
    }
    scope.expand();
    if let Ok(line) = try_still_valid(&end, &scope, n, !reqursion) {return Ok(line)}
    if reqursion {return Err(());}
    if let Ok(line) = try_false_elim(&end, &scope, n) {return Ok(line)}
    if let Ok(line) = try_raa(&end, scope.clone(), n) {return Ok(line)}

    Err(())
}
fn try_raa<'a>(end: &Operator<'a>, mut scope: Scope<'a>, n: usize) -> Result<Line<'a>, ()> {
    if end == &Operator::False {return Err(())}
    let inv = *Operator::invert(Box::new(end.clone()));
    scope.assume(inv);
    //println!("{}doing raa on {}", " ".repeat(n), end);
    match prove(Operator::False, scope.clone(), n) {
        Ok(proof) => {
            return Ok(Line::FalseElim(Box::new(proof), end.clone()));
        },
        Err(_) => {Err(())},
    }
}
fn try_false_elim<'a>(end: &Operator<'a>, scope: &Scope<'a>, n: usize) -> Result<Line<'a>, ()>{
    let false_proofs = scope.get(&Operator::False);
    if false_proofs.len() != 0 {
        'proof_loop:
        for mut proof in false_proofs {
            //println!("{}found false via {}", " ".repeat(n), proof);
            for missing in get_missing(&mut proof) {
                if let Err(end) = missing {
                    match prove(end.clone(), scope.clone(), n) {
                        Ok(new_line) => {
                            *missing = Ok(Box::new(new_line))
                        },
                        Err(_) => continue 'proof_loop,
                    }
                    
                }
            }
            return Ok(Line::FalseElim(Box::new(proof), end.clone()))
        }
    }
    Err(())
}
fn try_still_valid<'a>(end: &Operator<'a>, scope: &Scope<'a>, n: usize, can_requrse: bool) -> Result<Line<'a>, ()> {
    let proofs = scope.get(end);
    if proofs.len() != 0 {
        'proof_loop:
        for mut proof in proofs {
            //println!("{}found it via {}", " ".repeat(n), proof);
            for missing in get_missing(&mut proof) {
                if let Err(end) = missing {
                    if !can_requrse {return Err(());}
                    match prove(end.clone(), scope.clone(), n) {
                        Ok(new_line) => {
                            *missing = Ok(Box::new(new_line))
                        },
                        Err(_) => continue 'proof_loop,
                    }
                    
                }
            }
            return Ok(proof)
        }
    }
    Err(())
}
fn try_short_circuit<'a>(end: &Operator<'a>, mut scope: Scope<'a>, n: usize) -> Result<Line<'a>, ()> {
    match end.clone() {
        Operator::Implication(a, b) => {
            //println!("{}shortcut impl", " ".repeat(n));
            let asum = scope.assume(*a);
            let proof = prove(*b, scope, n)?;
            Ok(Line::ImplIntro(Box::new(proof), asum))
        },
        Operator::Not(a) => {
            //println!("{}shortcut not", " ".repeat(n));
            let asum = scope.assume(*Operator::invert(a));
            let proof = prove(Operator::False, scope, n)?;
            Ok(Line::NotIntro(Box::new(proof), asum))
        },
        Operator::All(var, mut domain, mut predicate) => {
            //println!("{}shortcut for all", " ".repeat(n));
            domain.bind(var.index, false);
            predicate.bind(var.index, false);
            let asum = scope.assume(*domain);
            scope.add_var(var);
            let proof = prove(*predicate, scope, n)?;
            Ok(Line::AllIntro(Box::new(proof), var, asum))
        },
        Operator::Exist(var, domain, predicate) => {
            //println!("{}shortcut exists", " ".repeat(n));
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
fn get_missing<'a, 'b>(line: &'b mut Line<'a>) -> Vec<&'b mut Result<Box<Line<'a>>, Operator<'a>>> {
    let mut v = Vec::new();
    match line {
        Line::ExElim(a, b) |
        Line::ImplElim(a, b) |
        Line::NotElim(a, b) => {
            v.append(&mut get_missing(a.as_mut()));
            v.push(b);
        }
        Line::AllElim(a, b, _) => {
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
        Line::DisjElim(_, a) |
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


impl<'a> Display for Set<'a> {
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
impl<'a> Display for Operator<'a> {
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
enum Statement<'a> {
    Block {
        hint: &'a str,
        assumption: Operator<'a>,
        inside: Box<Statement<'a>>,
        label: Operator<'a>
    },
    Line {
        previous: Vec<Box<Statement<'a>>>,
        hint: &'a str,
        label: Operator<'a>
    },
    StillValid {
        assumption: Operator<'a>
    }
}
impl<'a> Display for Statement<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Block { hint, assumption, inside, label } => {
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
                writeln!(f, "{{Assume:}}")?;
                writeln!(f, "{}", assumption)
            },
        }
    }
}
impl<'a> Line<'a> {
    fn render(&self) -> Option<Statement<'a>> {
        let hint = self.get_hint();
        let vls = match self {
            Line::Assume(_) => None,

            Line::ConjElim(_, a) |
            Line::BiImplElim(_, a) |
            Line::FalseElim(a, _) => Some(Ok(vec![a.render()])),

            Line::DisjElim(a, b) |
            Line::ConjIntro(a, b) |
            Line::BiImplInto(a, b) => Some(Ok(vec![a.render(), b.render()])),

            Line::AllElim(a, b, _) |
            Line::NotElim(a, b) |
            Line::ExElim(a, b) |
            Line::ImplElim(a, b) => Some(Ok(vec![a.render(), b.as_ref().unwrap().render()])),
            
            Line::DisjIntro(a, b) |
            Line::AllIntro(a, _, b) |
            Line::NotIntro(a, b) |
            Line::ImplIntro(a, b) |
            Line::ExIntro(a, _, b) => Some(Err((a.render().unwrap_or_else(|| Statement::StillValid { assumption: b.clone() }), b.clone()))),
        };
        let label = *self.get_label();
        match vls {
            Some(Ok(elms)) => {
                Some(Statement::Line { previous: elms.into_iter().flatten().map(Box::new).collect(), hint, label })
            },
            Some(Err((elm, assumption))) => {
                Some(Statement::Block { hint, assumption, inside: Box::new(elm), label })
            }
            _ => {None}
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
    fn get_label(&self) -> Box<Operator<'a>> {
        match self {
            Line::Assume(a) => Box::new(a.clone()),
            Line::ConjElim(_, _) => todo!(),
            Line::BiImplElim(_, _) => todo!(),
            Line::DisjElim(_, _) => todo!(),
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
            Line::NotIntro(_, _) => todo!(),
            Line::FalseElim(_, a) => Box::new(a.clone()),
        }
    }
}