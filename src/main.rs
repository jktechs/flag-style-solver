use std::time::SystemTime;

use sat_again::{
    logic::{DynLogic, Proof},
    *,
};

fn main() {
    let t = Bicond(
        Conj(
            Impl(Variable(0).wrap(), Variable(2).wrap()).wrap(),
            Impl(Variable(1).wrap(), Variable(2).wrap()).wrap(),
        )
        .wrap(),
        Impl(
            Disj(Variable(0).wrap(), Variable(1).wrap()).wrap(),
            Variable(2).wrap(),
        )
        .wrap(),
    )
    .wrap();
    println!("{t}");
    let proof = Proof::new(0, t);
    let now = SystemTime::now();
    for i in 0..20 {
        println!("{i}");
        let step = logic::step(&proof);
        if step != Some(false) {
            println!("{}", step.is_some());
            break;
        }
    }
    println!("{:?}", now.elapsed().unwrap()); // 160 / 580
    print!("{proof}");
}
#[test]
fn morgan_conj() {
    let t = Invert(Conj(Variable(0).wrap(), Invert(Variable(0).wrap()).wrap()).wrap()).wrap();
    let proof = Proof::new(1, t);
    loop {
        if let Some(val) = logic::step(&proof) {
            println!("{}", val);
            break;
        }
    }
}
#[test]
fn morgan_disj() {
    let t = Disj(Variable(0).wrap(), Invert(Variable(0).wrap()).wrap()).wrap();
    let proof = Proof::new(1, t);
    loop {
        if let Some(val) = logic::step(&proof) {
            println!("{}", val);
            break;
        }
    }
}
#[test]
fn invert() {
    use sat_again::logic::False;
    let t = Invert(False.wrap()).wrap();
    let proof = Proof::new(1, t);
    loop {
        if let Some(val) = logic::step(&proof) {
            println!("{}", val);
            break;
        }
    }
}
