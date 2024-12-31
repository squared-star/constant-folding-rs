extern crate pest;
#[macro_use]
extern crate pest_derive;

pub mod ast;
pub use ast::*;

pub mod parser;
pub use parser::*;

pub mod constant_folding;
pub use constant_folding::*;

use std::fs;

fn main() {
    // Fetch file string.
    let unparsed_file = fs::read_to_string("src/files/before.leo").expect("cannot read file");
    println!("Unparsed file:\n{:?}\n", unparsed_file);

    // Create AST from file string.
    let file = parse(&unparsed_file).expect("unsuccessful parse");

    // Perform constant folding.
    let file = file
        .constant_folding()
        .expect("unsuccessful constant folding");

    // Write program to output.
    println!("Resulting program:\n\n{}", file);
}
