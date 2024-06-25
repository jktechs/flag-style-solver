use std::{env, error::Error, io::stdin};

use logic_solver::{
    parser::{shunting_yard, solve, TokenIter},
    proof::{Proof, Scope},
};

fn main() -> Result<(), Box<dyn Error>> {
    let input = env::args()
        .nth(1)
        .map(Result::<String, std::io::Error>::Ok)
        .unwrap_or_else(|| {
            let mut buffer = String::new();
            stdin().read_line(&mut buffer)?;
            Ok(buffer)
        })?;
    let tokens = TokenIter(input.trim().chars().enumerate());
    let polish = shunting_yard(tokens);
    let expr = solve(polish);
    if let Some(proof) = Proof::new(&expr, &Scope::empty()) {
        println!("{}", proof);
        Ok(())
    } else {
        Err("No proof found.".into())
    }
}
