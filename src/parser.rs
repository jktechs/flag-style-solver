//! This module is responsible for parsing input into logical expressions.

use std::collections::VecDeque;

use crate::{
    expressions::{DynExpression, Expression},
    proposition::{Bicond, Conj, Disj, False, Impl, Inv, True, Var},
};

#[derive(Debug)]
/// All tokens in a logical expression.
pub enum Token {
    /// The conjunction operator: ∧, /\
    Conj,
    /// The Disjunction operator: ∨, \/
    Disj,
    /// The Inversion operator: ¬, !
    Inv,
    /// The Biconditional operator: ⇔, <=>
    Bicond,
    /// The Implication operator: ⇒, =>
    Impl,
    /// An open bracket: (
    Open,
    /// A close bracket: )
    Close,
    /// A variable, e.g. 'P'
    Var(char),
    /// The thruth value: ⊤
    True,
    /// The Contridicting value: ⊥
    False,
}
impl Token {
    /// Returns weather a token is an operator and what its presidence is. (higher means earlier.)
    fn operator(&self) -> Option<usize> {
        match self {
            Self::Inv => Some(3),
            Self::Conj | Self::Disj => Some(2),
            Self::Impl => Some(1),
            Self::Bicond => Some(0),
            _ => None,
        }
    }
    /// Returns weather this token is a unairy operator.
    fn unairy(&self) -> bool {
        matches!(self, Self::Inv)
    }
    /// Returns weather this is a bracket and if it is open.
    fn bracket_open(&self) -> Option<bool> {
        match self {
            Self::Open => Some(true),
            Self::Close => Some(false),
            _ => None,
        }
    }
}
/// Iterates over Tokens of a indexed character iterator.
pub struct TokenIter<I: Iterator<Item = (usize, char)>>(pub I);
impl<I: Iterator<Item = (usize, char)>> Iterator for TokenIter<I> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        match self.0.next() {
            Some((i, '=')) => {
                assert_eq!(self.0.next()?.1, '>', "Expected '>' at {}", i + 1);
                Some(Token::Impl)
            }
            Some((i, '/')) => {
                assert_eq!(self.0.next()?.1, '\\', "Expected '\\' at {}", i + 1);
                Some(Token::Conj)
            }
            Some((i, '\\')) => {
                assert_eq!(self.0.next()?.1, '/', "Expected '/' at {}", i + 1);
                Some(Token::Disj)
            }
            Some((i, '<')) => {
                assert_eq!(self.0.next()?.1, '=', "Expected '=' at {}", i + 1);
                assert_eq!(self.0.next()?.1, '>', "Expected '>' at {}", i + 2);
                Some(Token::Bicond)
            }
            Some((i, '!')) => Some(Token::Inv),
            Some((i, ')')) => Some(Token::Close),
            Some((i, '(')) => Some(Token::Open),
            Some((i, 'F')) => Some(Token::False),
            Some((i, 'T')) => Some(Token::True),
            Some((i, x)) if x.is_alphabetic() && x.is_uppercase() => Some(Token::Var(x)),
            Some((i, _)) => panic!("Unkown character at {i}"),
            None => None,
        }
    }
}

/// Parses a Token iterator into reverse polish notation.
pub fn shunting_yard<I: Iterator<Item = Token>>(mut tokens: I) -> Vec<Token> {
    let mut holding_stack = Vec::new();
    let mut output = Vec::new();

    for token in tokens {
        if let Some(priority) = token.operator() {
            while holding_stack
                .last()
                .and_then(Token::operator)
                .unwrap_or_default()
                > priority
            {
                if let Some(token) = holding_stack.pop() {
                    output.push(token);
                }
            }
            holding_stack.push(token);
        } else if let Some(open) = token.bracket_open() {
            if open {
                holding_stack.push(token);
            } else {
                while let Some(token) = holding_stack.pop() {
                    if let Some(true) = token.bracket_open() {
                        break;
                    }
                    output.push(token);
                }
            }
        } else {
            output.push(token);
        }
    }
    while let Some(token) = holding_stack.pop() {
        output.push(token);
    }
    output
}
#[must_use]
/// Solves the reverse polish notation into a logic expression.
/// # Panics
/// If the input is not valid reverse polish notation.
pub fn solve(tokens: Vec<Token>) -> Expression {
    let mut stack = Vec::new();
    for i in tokens {
        match i {
            Token::Conj => {
                let a = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                stack.push(Conj(b, a).wrap());
            }
            Token::Disj => {
                let a = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                stack.push(Disj(b, a).wrap());
            }
            Token::Inv => {
                let a = stack.pop().unwrap();
                stack.push(Inv(a).wrap());
            }
            Token::Bicond => {
                let a = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                stack.push(Bicond(b, a).wrap());
            }
            Token::Impl => {
                let a = stack.pop().unwrap();
                let b = stack.pop().unwrap();
                stack.push(Impl(b, a).wrap());
            }
            Token::Var(c) => stack.push(Var(c).wrap()),
            Token::True => stack.push(True.wrap()),
            Token::False => stack.push(False.wrap()),
            _ => {}
        }
    }
    stack.pop().unwrap()
}
