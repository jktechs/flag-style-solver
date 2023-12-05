use std::{fmt::Display, collections::{VecDeque, HashMap, HashSet}, borrow::Cow};

#[derive(Clone)]
struct Scope {
    vars: HashSet<Variable>,
    map: HashMap<Predicate, >
}

#[derive(Debug, Hash, PartialEq, Eq)]
struct Predicate<'a> {
    logic: Vec<LogicOperator<'a>>,
    set: Vec<SetOperator<'a>>,
    root: usize
}
impl<'a> Display for Predicate<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_formula(f, &self.logic, &self.set, DisplayElm::Logic(&self.logic[self.root]))
    }
}
#[derive(Debug, Hash, PartialEq, Eq)]
struct Set<'a> {
    logic: Vec<LogicOperator<'a>>,
    set: Vec<SetOperator<'a>>,
    root: usize
}
impl<'a> Display for Set<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        display_formula(f, &self.logic, &self.set, DisplayElm::Set(&self.set[self.root]))
    }
}
enum DisplayElm<'a, 'b> {
    String(Cow<'a,str>),
    Logic(&'b LogicOperator<'a>),
    Set(&'b SetOperator<'a>)
}
fn display_formula(f: &mut std::fmt::Formatter<'_>, logic: &Vec<LogicOperator<'_>>, set: &Vec<SetOperator<'_>>, root: DisplayElm<'_,'_>) -> std::fmt::Result {
    let mut stack = VecDeque::new();
    stack.push_back(root);

    while let Some(val) = stack.pop_back() {
        use LogicOperator::*;
        use SetOperator::*;
        use DisplayElm::*;

        match &val {
            Logic(Conjunction(a, b)) => {stack.extend(vec![String(")".into()), Logic(&logic[*b]), String("/\\".into()), Logic(&logic[*a]), String("(".into())])},
            Logic(Disjunction(a, b)) => {stack.extend(vec![String(")".into()), Logic(&logic[*b]), String("\\/".into()), Logic(&logic[*a]), String("(".into())])},
            Logic(Implication(a, b)) => {stack.extend(vec![String(")".into()), Logic(&logic[*b]), String("=>".into()), Logic(&logic[*a]), String("(".into())])},
            Logic(BiImplication(a, b)) => {stack.extend(vec![String(")".into()), Logic(&logic[*b]), String("<=>".into()), Logic(&logic[*a]), String("(".into())])},
            Logic(Not(a)) => {stack.extend(vec![String(")".into()), String("!".into()), Logic(&logic[*a]), String("(".into())])},
            Logic(False) => {stack.push_back(String("False".into()))},
            Logic(True) => {stack.push_back(String("False".into()))},
            Logic(Predicate(a, b)) => {stack.extend(vec![String(")".into()), String(b.to_string().into()), String("(".into()), String((*a).into())])},
            Logic(LogicVariable(a)) => {stack.push_back(String((*a).into()))},
            Logic(All(a, b, c)) => {stack.extend(vec![String("]".into()), Logic(&logic[*c]), String(": ".into()), Logic(&logic[*b]), String("[".into()), String(a.to_string().into()), String("∀".into())])},
            Logic(Exist(a, b, c)) => {stack.extend(vec![String("]".into()), Logic(&logic[*c]), String(": ".into()), Logic(&logic[*b]), String("[".into()), String(a.to_string().into()), String("Ǝ".into())])},

            Logic(Subset(a, b)) => {},
            Logic(Equals(a, b)) => {},
            Logic(In(a, b)) => {},

            Set(SetVariable(a)) => {},
            Set(Intersection(a, b)) => {},
            Set(Union(a, b)) => {},
            Set(Difference(a)) => {},
            
            Set(Def(a, b)) => {}, // first set then operation

            String(a) => {write!(f, "{}", a)?;}
        }
    }

    Ok(())
}
type Variable = u32;
#[derive(Debug, Hash, PartialEq, Eq)]
enum LogicOperator<'a> {
    Conjunction(usize, usize),
    Disjunction(usize, usize),
    Implication(usize, usize),
    BiImplication(usize, usize),
    Not(usize),
    False,
    True,
    Predicate(&'a str, Variable),
    LogicVariable(&'a str),
    All(Variable, usize, usize),
    Exist(Variable, usize, usize),

    Subset(usize, usize),
    Equals(usize, usize),
    In(Variable, usize),
}
#[derive(Debug, Hash, PartialEq, Eq)]
enum SetOperator<'a> {
    SetVariable(&'a str),
    Intersection(usize, usize),
    Union(usize, usize),
    Difference(usize),
    
    Def(usize, usize), // first set then operation
}
fn prove<'a>(end: Predicate) {
    let mut to_prove = Vec::new();
    let mut proven = HashMap::new();
    to_prove

    while let Some(val) = to_prove.pop() {

    }

}
fn main() {
    // (Vx[x in N:P(x)]=>Ey[y in N:Q(y)]) => Ez[z in N: P(z) => Q(z)]
    let mut p = Vec::new();
    p.push(LogicOperator::Predicate("P", 0));  //0
    p.push(LogicOperator::Predicate("P", 2));  //1
    p.push(LogicOperator::Predicate("Q", 1));  //2
    p.push(LogicOperator::Predicate("Q", 2));  //3
    p.push(LogicOperator::Predicate("N", 0));  //4
    p.push(LogicOperator::Predicate("N", 1));  //5
    p.push(LogicOperator::Predicate("N", 2));  //6
    p.push(LogicOperator::Implication(1, 3));  //7
    p.push(LogicOperator::All(0, 4, 0));       //8
    p.push(LogicOperator::Exist(1, 5, 2));     //9
    p.push(LogicOperator::Exist(2, 6, 7));     //10
    p.push(LogicOperator::Implication(8, 9));  //11
    p.push(LogicOperator::Implication(11, 10));//12
    println!("{}", Predicate {logic: p, set: Vec::new(), root: 12 });
}