#[macro_use]
mod cnf;
mod ordinal;
mod ordinal_parser;

use std::io::stdin;

fn main() {
    let mut s = String::new();
    stdin().read_line(&mut s).unwrap();
    let (e1, e2) = ordinal_parser::parse_equation(&s).unwrap();
    println!("{}",
             if e1 == e2 {
                 "Равны"
             } else {
                 "Не равны"
             })
}
