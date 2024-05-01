use std::{sync::Arc, time::SystemTime};

use sat_again::{
    logic::{BlockProof, DynLogic, False, LineProof, Logic, Proof, ProofBranch},
    *,
};

fn step(x: &Logic, scope: &Arc<BlockProof>) -> Vec<Proof> {
    // intro
    let mut proofs = x.0.clone().intro(scope);
    // elim
    proofs.extend(
        scope
            .proof(x)
            .into_iter()
            .map(|p| p.deep_clone())
            .collect::<Vec<_>>(),
    );
    //  false elim
    proofs.extend(
        scope
            .proof(&False.wrap())
            .into_iter()
            .map(|p| p.deep_clone())
            .map(|p| {
                Proof::Line(LineProof::new(
                    x.clone(),
                    scope.clone(),
                    [ProofBranch::One(p)],
                ))
            })
            .collect::<Vec<Proof>>(),
    );
    //  contridiction
    proofs.push(Proof::Block(BlockProof::new(
        x.0.clone().invert(),
        x.clone(),
        scope.clone(),
        ProofBranch::Possible(False.wrap()),
    )));
    proofs.retain(|p| p.valid());
    proofs
}

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
        if let Some(val) = logic::step(&proof, &step) {
            println!("{}", val);
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
        if let Some(val) = logic::step(&proof, &step) {
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
        if let Some(val) = logic::step(&proof, &step) {
            println!("{}", val);
            break;
        }
    }
}
#[test]
fn invert() {
    let t = Invert(False.wrap()).wrap();
    let proof = Proof::new(1, t);
    loop {
        if let Some(val) = logic::step(&proof, &step) {
            println!("{}", val);
            break;
        }
    }
}
