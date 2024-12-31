use crate::ast::*;
use pest::error::Error;
use pest::iterators::Pair;
use pest::Parser;

// The pest parser for Leo

#[derive(Parser)]
#[grammar = "leo.pest"]
pub struct LeoParser;

// Functions to parse a Leo code string into a Leo AST

pub fn parse(source: &str) -> Result<Program, Error<Rule>> {
    let mut name = String::new();
    let mut inputs = Vec::new();
    let mut statements = Vec::new();

    let pairs = LeoParser::parse(Rule::program, source)?;

    for pair in pairs {
        match pair.as_rule() {
            Rule::function_header => {
                let mut pair = pair.into_inner();

                // Parse function name
                name = pair.next().unwrap().as_str().to_string();

                // Parse function inputs if any
                if let Some(pair) = pair.next() {
                    inputs = parse_inputs(pair);
                }
            }
            Rule::statement => {
                statements.push(parse_statement(pair.into_inner().next().unwrap()));
            }
            _ => {}
        }
    }

    Ok(Program {
        name,
        inputs,
        statements,
    })
}

fn parse_inputs(pair: pest::iterators::Pair<Rule>) -> Vec<Input> {
    let mut inputs = Vec::new();

    for pair in pair.into_inner() {
        let rule = pair.as_rule();
        println!("{:?}", rule);
        match rule {
            Rule::input => {
                let mut pair = pair.into_inner();

                let name = pair.next().unwrap().as_str().to_string();
                let input_type = parse_type(pair.next().unwrap());

                inputs.push(Input { name, input_type });
            }
            _ => {}
        }
    }

    inputs
}

fn parse_type(pair: pest::iterators::Pair<Rule>) -> Type {
    match pair.as_str() {
        "u8" => Type::U8,
        _ => panic!("failed to parse type"),
    }
}

fn parse_statement(pair: pest::iterators::Pair<Rule>) -> Statement {
    match pair.as_rule() {
        Rule::assign => {
            let mut pair = pair.into_inner();

            let variable = pair.next().unwrap().as_str().to_string();
            let expression = parse_expression(pair.next().unwrap());

            Statement::Assign {
                variable,
                expression,
            }
        }
        _ => panic!("failed to parse statement"),
    }
}

fn parse_expression(pair: pest::iterators::Pair<Rule>) -> Expression {
    match pair.as_rule() {
        Rule::expression => {
            let pair = pair.into_inner().next().unwrap();

            match pair.as_rule() {
                Rule::binary => parse_binary(pair),
                Rule::value => {
                    Expression::Value(Box::new(parse_value(pair.into_inner().next().unwrap())))
                }
                Rule::integer | Rule::ident => Expression::Value(Box::new(parse_value(pair))),
                Rule::expression => Expression::Value(Box::new(Value::Expression(Box::new(
                    parse_expression(pair),
                )))),
                _ => {
                    panic!(
                        "failed to parse inner expression: {:?}, {:?}",
                        pair.as_str(),
                        pair
                    )
                }
            }
        }
        Rule::value => Expression::Value(Box::new(parse_value(pair.into_inner().next().unwrap()))),
        Rule::binary => parse_binary(pair),
        Rule::integer | Rule::ident => Expression::Value(Box::new(parse_value(pair))),
        _ => panic!(
            "failed to parse expression: {:?}, {:?}",
            pair.as_str(),
            pair
        ),
    }
}

fn parse_binary(pair: Pair<Rule>) -> Expression {
    let mut pair = pair.into_inner();

    let left = parse_value(pair.next().unwrap());
    let operator = parse_operator(pair.next().unwrap());
    let right = Box::new(parse_expression(pair.next().unwrap()));

    Expression::Binary {
        left,
        operator,
        right,
    }
}

fn parse_value(pair: pest::iterators::Pair<Rule>) -> Value {
    match pair.as_rule() {
        Rule::integer => {
            // Parse the integer and trim the value type
            let int_str = pair.as_str();
            let int_len = int_str.len();
            let integer = &int_str[..int_len - 2].parse::<u8>().unwrap();

            Value::Integer(*integer)
        }
        Rule::ident => {
            let ident = pair.as_str().to_string();

            Value::Identifier(ident)
        }
        Rule::expression => {
            let expression = parse_expression(pair);

            Value::Expression(Box::new(expression))
        }
        _ => panic!("failed to parse value: {}, {:?}", pair.as_str(), pair),
    }
}

fn parse_operator(pair: pest::iterators::Pair<Rule>) -> Operator {
    match pair.as_str() {
        "+" => Operator::Add,
        "-" => Operator::Subtract,
        "*" => Operator::Multiply,
        "/" => Operator::Divide,
        _ => panic!("failed to parse operator"),
    }
}
