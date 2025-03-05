use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub grammar);
pub mod ast;

fn print(s: &str) {
    let res = grammar::ExprParser::new().parse(s).unwrap();
    println!("Term: {:?}", res);
    println!("Type: {:?}",crate::ast::check_main(&res));
    println!("");
}

fn main() {
   print("Π (n: *), Σ (x: *), n");
   print("Σ (y x: *), *");
}
