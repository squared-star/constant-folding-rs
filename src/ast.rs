// The Abstract Syntax Tree (AST) for Leo

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Program {
    // function main(a: u8) {
    //     let b = a + 1u8;
    // }
    pub name: String,
    pub inputs: Vec<Input>,
    pub statements: Vec<Statement>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct Input {
    pub name: String,
    pub input_type: Type,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Type {
    U8,
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Statement {
    // let a = 1u8;
    Assign {
        variable: String,
        expression: Expression,
    },
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Expression {
    // 1u8 + 2u8
    Binary {
        left: Value,
        operator: Operator,
        right: Box<Expression>,
    },
    // 1u8
    Value(Box<Value>),
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Value {
    // 1u8
    Integer(u8),
    // a
    Identifier(String),
    // (1u8 + a)
    Expression(Box<Expression>),
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
pub enum Operator {
    Add,
    Subtract,
    Multiply,
    Divide,
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let inputs = self
            .inputs
            .iter()
            .map(|input| format!("{:?}: {:?}", input.name, input.input_type))
            .collect::<Vec<String>>()
            .join(", ");

        let statements = self
            .statements
            .iter()
            .map(|statement| format!("    {}", statement))
            .collect::<Vec<String>>()
            .join("\n");

        write!(
            f,
            "function {}({}) {{\n{}\n}}",
            self.name, inputs, statements
        )
    }
}

impl std::fmt::Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Statement::Assign {
                variable,
                expression,
            } => {
                write!(f, "let {} = {};", variable, expression)
            }
        }
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expression::Binary {
                left,
                operator,
                right,
            } => {
                write!(f, "{} {} {}", left, operator, right)
            }
            Expression::Value(value) => {
                write!(f, "{}", value)
            }
        }
    }
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Operator::Add => {
                write!(f, "+")
            }
            Operator::Subtract => {
                write!(f, "-")
            }
            Operator::Multiply => {
                write!(f, "*")
            }
            Operator::Divide => {
                write!(f, "/")
            }
        }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Integer(integer) => {
                write!(f, "{}u8", integer)
            }
            Value::Identifier(identifier) => {
                write!(f, "{}", identifier)
            }
            Value::Expression(expression) => {
                write!(f, "({})", expression)
            }
        }
    }
}
