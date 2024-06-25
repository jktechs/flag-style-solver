#![warn(clippy::pedantic, missing_docs, clippy::missing_docs_in_private_items)]
#![allow(unused)]
//! This crates allows for expressing logical statements and proving them to be true.

use std::{fmt::Pointer, io::stdout, sync::Arc};

use expressions::{DynExpression, Expression};
use parser::{shunting_yard, solve, TokenIter};
use proof::{Proof, Scope};
use proposition::{Bicond, Conj, Disj, Impl, Inv, True, Var};

pub mod expressions;
pub mod parser;
pub mod proof;
pub mod proposition;

#[test]
fn parse_expr() {
    let pol = shunting_yard(TokenIter(
        "(((P=>R)/\\(Q=>R))<=>((P\\/Q)=>R))".chars().enumerate(),
    ));
    println!("{}", solve(pol));
    let pol = shunting_yard(TokenIter("T/\\!!T".chars().enumerate()));
    println!("{}", solve(pol));
}

#[test]
fn test_truth() {
    println!("{}", Proof::new(&True.wrap(), &Scope::empty()).unwrap());
}
#[test]
fn test_double_inversion() {
    println!(
        "{}",
        Proof::new(&Inv(Inv(True.wrap()).wrap()).wrap(), &Scope::empty()).unwrap()
    );
}
#[test]
fn test_excluded_middle() {
    println!(
        "{}",
        Proof::new(
            &Disj(Var('P').wrap(), Inv(Var('P').wrap()).wrap()).wrap(),
            &Scope::empty(),
        )
        .unwrap()
    );
}
#[test]
fn test_implication_compression() {
    println!(
        "{}",
        Proof::new(
            &Impl(
                Conj(
                    Impl(Var('P').wrap(), Var('Q').wrap()).wrap(),
                    Impl(Var('Q').wrap(), Var('R').wrap()).wrap()
                )
                .wrap(),
                Impl(Var('P').wrap(), Var('R').wrap()).wrap()
            )
            .wrap(),
            &Scope::empty(),
        )
        .unwrap()
    );
}
#[test]
fn test_implication_distribution() {
    let expr = Bicond(
        Conj(
            Impl(Var('P').wrap(), Var('R').wrap()).wrap(),
            Impl(Var('Q').wrap(), Var('R').wrap()).wrap(),
        )
        .wrap(),
        Impl(
            Disj(Var('P').wrap(), Var('Q').wrap()).wrap(),
            Var('R').wrap(),
        )
        .wrap(),
    )
    .wrap();
    let proof = Proof::new(&expr, &Scope::empty());
    println!("{}", proof.unwrap());
}
#[test]
fn test_cashe() {
    let t_a = True.wrap();
    let t_b = True.wrap();
    assert_eq!(format!("{t_a:p}"), format!("{t_b:p}"));
}
