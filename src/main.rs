use std::io::Write;
use sat::{Predicate, prove, Variable};

fn main() {
    let x = Variable {index: 0, bound: true};
    let y = Variable {index: 1, bound: true};
    let z = Variable {index: 2, bound: true};
    let root = Predicate::Implication(Box::new(Predicate::Implication(Box::new(Predicate::All(x.clone(), Box::new(Predicate::PredicateVariable("N".into(), x.clone())), Box::new(Predicate::PredicateVariable("P".into(), x.clone())))), Box::new(Predicate::Exist(y.clone(), Box::new(Predicate::PredicateVariable("N".into(), y.clone())), Box::new(Predicate::PredicateVariable("Q".into(), y.clone())))))), Box::new(Predicate::Exist(z.clone(), Box::new(Predicate::PredicateVariable("N".into(), z.clone())), Box::new(Predicate::Implication(Box::new(Predicate::PredicateVariable("P".into(), z.clone())),Box::new(Predicate::PredicateVariable("Q".into(), z.clone())))) )));
    //let root = Predicate::Implication(Box::new(Predicate::Conjunction(Box::new(Predicate::Conjunction(Box::new(Predicate::Implication(Box::new(Predicate::Variable("P".into())), Box::new(Predicate::Variable("Z".into())))), Box::new(Predicate::Implication(Box::new(Predicate::Variable("Q".into())), Box::new(Predicate::Variable("Z".into())))))), Box::new(Predicate::Disjunction(Box::new(Predicate::Variable("P".into())), Box::new(Predicate::Variable("Q".into())))))), Box::new(Predicate::Variable("Z".into())));
    println!("{}", &root);
    let proof = prove(root);
    let mut file = std::fs::File::create("log.txt").unwrap();
    file.write_all(proof.to_string().as_bytes()).unwrap();
    println!("{}", proof);
}