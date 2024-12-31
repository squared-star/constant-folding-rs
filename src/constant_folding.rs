use std::collections::HashMap;

use crate::{Expression, Operator, Program, Statement, Value};

/// The symbol table is a mapping from variable names to their constant values. Variables that are not
/// statically known are not present in the symbol table.
type SymbolTable = HashMap<String, u8>;

impl Operator {
    /// Performs a constant folding operation on two `u8` constants using the specified operator.
    ///
    /// This function applies the operator to the provided constants, attempting to perform the operation
    /// while checking for potential errors such as overflow or division by zero. The function returns the
    /// result of the operation if successful, or an error if the operation cannot be performed safely.
    ///
    /// # Parameters
    ///
    /// - `self`: The operator to apply to the constants. This can be one of the following:
    ///   - `Operator::Multiply`: Multiplies the two constants.
    ///   - `Operator::Divide`: Divides the first constant by the second.
    ///   - `Operator::Add`: Adds the two constants together.
    ///   - `Operator::Subtract`: Subtracts the second constant from the first.
    /// - `constant0`: The first `u8` constant to be used in the operation.
    /// - `constant1`: The second `u8` constant to be used in the operation.
    ///
    /// # Returns
    ///
    /// A `Result<u8, ConstantFoldingError>`:
    /// - `Ok(u8)` containing the result of the operation if successful.
    /// - `Err(ConstantFoldingError)` if an error occurs during the operation:
    ///   - `ConstantFoldingError::Overflow`: If the operation results in an overflow.
    ///   - `ConstantFoldingError::DivisionByZero`: If a division by zero is attempted.
    ///
    /// # Errors
    ///
    /// This function may return a `ConstantFoldingError` in the following situations:
    /// - `Overflow`: If the result of multiplication, addition, or subtraction exceeds the maximum value
    ///   for a `u8`.
    /// - `DivisionByZero`: If a division by zero is attempted.
    pub fn fold_constants(self, constant0: u8, constant1: u8) -> Result<u8, ConstantFoldingError> {
        use Operator as O;
        match self {
            O::Multiply => constant0
                .checked_mul(constant1)
                .ok_or(ConstantFoldingError::Overflow),
            O::Divide => constant0
                .checked_div(constant1)
                .ok_or(ConstantFoldingError::DivisionByZero),
            O::Add => constant0
                .checked_add(constant1)
                .ok_or(ConstantFoldingError::Overflow),
            O::Subtract => constant0
                .checked_sub(constant1)
                .ok_or(ConstantFoldingError::Overflow),
        }
    }
}

/// Constant folding can reveal flaws in code that would otherwise be hidden until runtime.
/// This enum represents the different types of errors that can occur during constant folding operations.
///
/// This enum is used to handle errors that might arise when performing constant folding in an
/// expression. Constant folding is an optimization technique where constant expressions are
/// evaluated at compile time rather than runtime.
///
/// # Variants
///
/// - `Overflow`: This error occurs when an arithmetic operation (such as addition or multiplication)
///   results in a value that exceeds the maximum value that can be stored in the type (e.g., `u8`).
///
/// - `DivisionByZero`: This error occurs when a division operation attempts to divide by zero, which
///   is undefined and results in an error.
#[derive(Debug, PartialEq, Eq)]
pub enum ConstantFoldingError {
    Overflow,
    DivisionByZero,
}

impl Program {
    /// Performs constant folding on the statements in a program, optimizing expressions by evaluating
    /// constant expressions at compile time.
    ///
    /// This function iterates over each statement in the program, applies constant folding to optimize
    /// any constant expressions, and updates the symbol table with known values. The result is a new
    /// program with optimized statements where possible.
    ///
    /// # Returns
    ///
    /// A `Result<Program, ConstantFoldingError>`:
    /// - `Ok(Program)` if all statements were successfully folded without encountering errors.
    /// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow or division by zero.
    ///
    /// # Errors
    ///
    /// This function may return a `ConstantFoldingError` if:
    /// - An arithmetic operation overflows (e.g., an addition or multiplication results in a value too large for the type).
    /// - A division by zero is attempted.
    pub fn constant_folding(self) -> Result<Program, ConstantFoldingError> {
        let Program {
            name,
            inputs,
            statements,
        } = self;

        // Create a symbol table to store the values of variables that are known at compile time.
        let mut symbols = SymbolTable::new();

        // Perform constant folding on each statement.
        let statements = statements
            .into_iter()
            .map(move |statement| statement.constant_folding(&mut symbols))
            .collect::<Result<_, _>>()?;

        // Return the program with the constant-folded statements.
        Ok(Program {
            name,
            inputs,
            statements,
        })
    }
}
impl Statement {
    /// Performs constant folding on a single statement, optimizing expressions by evaluating
    /// constant expressions at compile time and updating the symbol table with known values.
    ///
    /// This function processes an assignment statement, attempts to optimize the expression on the
    /// right-hand side, and updates the symbol table with the result if it resolves to a constant
    /// integer value. The optimized statement is then returned.
    ///
    /// # Parameters
    ///
    /// - `self`: The `Statement` to be processed for constant folding.
    /// - `symbols`: A mutable reference to the `SymbolTable` that stores variable values known at
    ///   compile time. This table is updated with new values as they are discovered during constant
    ///   folding.
    ///
    /// # Returns
    ///
    /// A `Result<Statement, ConstantFoldingError>`:
    /// - `Ok(Statement)` containing the optimized statement if the folding is successful.
    /// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow
    ///   or division by zero.
    ///
    /// # Errors
    ///
    /// This function may return a `ConstantFoldingError` if:
    /// - An arithmetic operation overflows (e.g., an addition or multiplication results in a value too large for the type).
    /// - A division by zero is attempted.
    pub fn constant_folding(
        self,
        symbols: &mut SymbolTable,
    ) -> Result<Statement, ConstantFoldingError> {
        use Expression as E;
        use Statement as S;
        use Value as V;
        match self {
            S::Assign {
                variable,
                expression,
            } => {
                let expression = expression_constant_folding(expression, symbols, None)?;
                if let E::Value(v) = &expression {
                    if let V::Integer(value) = &**v {
                        symbols.insert(variable.clone(), *value);
                    }
                }
                Ok(S::Assign {
                    variable,
                    expression,
                })
            }
        }
    }
}

impl Expression {
    /// Returns an iterator over the operations (operator and value pairs) within a binary expression.
    ///
    /// This function traverses the binary expression tree, yielding each operator along with the associated
    /// value on the left-hand side. The iterator continues until all operations in the expression have been
    /// visited. This is particularly useful for analyzing or transforming complex expressions by examining
    /// the sequence of operations applied.
    ///
    /// # Returns
    ///
    /// An iterator that yields tuples of `(Operator, &Value)`, where:
    /// - `Operator` is the operator applied in the binary expression (e.g., `Add`, `Subtract`, `Multiply`, `Divide`).
    /// - `&Value` is a reference to the value associated with the operator.
    ///
    /// The iterator continues to yield these pairs until the entire expression has been traversed.
    ///
    /// # Note
    ///
    /// This function only traverses binary expressions. If the expression is a single value with no operators,
    /// the iterator will yield nothing. Additionally, the order of traversal is left-to-right as per the structure
    /// of the binary expression.
    fn operations(&self) -> impl Iterator<Item = (Operator, &Value)> {
        let mut state = match self {
            Expression::Value(_) => None,
            Expression::Binary {
                operator, right, ..
            } => Some((*operator, &**right)),
        };
        std::iter::from_fn(move || match state.take() {
            Some((current_operator, right)) => match right {
                Expression::Binary {
                    operator: next_operator,
                    right,
                    left,
                } => {
                    state = Some((*next_operator, right));
                    Some((current_operator, left))
                }
                Expression::Value(left) => Some((current_operator, left)),
            },
            None => None,
        })
    }
}
/// Performs constant folding on an expression, optimizing it by evaluating constant expressions
/// at compile time using the provided symbol table.
///
/// This function recursively processes an `Expression` by folding constant values and simplifying
/// expressions where possible. If the expression is a binary operation, it attempts to reduce the
/// expression based on the operators involved and the values found in the symbol table. The function
/// supports various arithmetic operations and handles different cases based on the initial operator.
///
/// # Parameters
///
/// - `expression`: The `Expression` to be processed for constant folding. This can be a simple value
///   or a more complex binary expression.
/// - `symbols`: A reference to the `SymbolTable` that holds known variable values. This table is used
///   to resolve identifiers to their constant values, if available.
/// - `initial_operator`: An `Option<Operator>` representing the operator directly to the left of the
///   expression fragment. If `None`, the expression is treated as closed; otherwise, the operator
///   influences how the expression is folded.
///
/// # Returns
///
/// A `Result<Expression, ConstantFoldingError>`:
/// - `Ok(Expression)` containing the optimized expression if the folding is successful.
/// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow
///   or division by zero.
///
/// # Errors
///
/// This function may return a `ConstantFoldingError` if:
/// - An arithmetic operation results in an overflow.
/// - A division by zero is attempted.
///
/// # Note
///
/// - This function supports handling various arithmetic operations such as addition, subtraction,
///   multiplication, and division. It also respects operator precedence and attempts to reduce
///   expressions as much as possible.
/// - When dealing with binary expressions, this function delegates part of the work to
///   `binary_constant_folding` to handle complex cases.
fn expression_constant_folding(
    expression: Expression,
    symbols: &SymbolTable,
    initial_operator: Option<Operator>, // None means closed expression; otherwise, it means the operator directly to the left of the expression fragment
) -> Result<Expression, ConstantFoldingError> {
    use Expression as E;
    use Operator as O;
    use Value as V;
    match expression {
        E::Value(v) => match value_constant_folding(*v, symbols)? {
            V::Integer(value) => Ok(E::Value(Box::new(V::Integer(value)))),
            V::Identifier(identifier) => Ok(E::Value(Box::new(V::Identifier(identifier)))),
            V::Expression(e) => match *e {
                E::Value(v) => Ok(E::Value(v)), // remove redundant parentheses
                E::Binary { .. } => match initial_operator {
                    // un-parenthesize if precedence compatible
                    Some(O::Add)
                        if e.operations().all(|(operator, _)| {
                            matches!(operator, O::Add | O::Multiply | O::Divide)
                        }) =>
                    {
                        Ok(*e)
                    }
                    Some(O::Multiply) if is_monomial(&e) => Ok(*e),
                    // Otherwise, leave in parentheses
                    None | Some(O::Divide) | Some(O::Subtract) | Some(O::Add | O::Multiply) => {
                        Ok(E::Value(Box::new(V::Expression(e))))
                    }
                },
            },
        },
        E::Binary {
            left,
            operator,
            right,
        } => {
            let left = value_constant_folding(left, symbols)?;
            let right = expression_constant_folding(*right, symbols, Some(operator))?;

            binary_constant_folding(initial_operator, operator, left, right)
        }
    }
}
/// Performs constant folding on binary expressions, optimizing arithmetic operations by evaluating
/// constants at compile time. This function recursively processes the left and right sides of the
/// expression, simplifying and reducing where possible based on the operators involved.
///
/// The function handles a wide range of binary operations, including addition, subtraction,
/// multiplication, and division. It also respects operator precedence and applies transformations
/// such as commutativity and associativity to reduce the complexity of expressions.
///
/// # Parameters
///
/// - `initial_operator`: An `Option<Operator>` representing the operator directly to the left of the
///   expression fragment. If `None`, the expression is treated as closed; otherwise, the operator
///   influences how the expression is folded.
/// - `operator`: The current `Operator` being applied to the `left` value and `right` expression.
/// - `left`: The left-hand `Value` of the binary expression.
/// - `right`: The right-hand `Expression` of the binary expression.
///
/// # Returns
///
/// A `Result<Expression, ConstantFoldingError>`:
/// - `Ok(Expression)` containing the optimized expression if the folding is successful.
/// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow
///   or division by zero.
///
/// # Errors
///
/// This function may return a `ConstantFoldingError` in the following situations:
/// - `Overflow`: If the result of an arithmetic operation exceeds the maximum value for a `u8`.
/// - `DivisionByZero`: If a division by zero is attempted.
///
/// # Notes
///
/// - This function applies various optimizations, such as commutativity and associativity, to simplify
///   expressions. For example, it might reorder terms to group constants together.
/// - The function operates in a loop, continuously simplifying the expression until no further reductions
///   are possible. In cases where complex binary expressions are encountered, the function may delegate
///   further processing to other functions.
fn binary_constant_folding(
    initial_operator: Option<Operator>,
    mut operator: Operator,
    mut left: Value,
    mut right: Expression,
) -> Result<Expression, ConstantFoldingError> {
    use Expression as E;
    use Operator as O;
    use Value as V;
    loop {
        // println!("Evaluating {}, {}, {}", left, operator, right);
        match (initial_operator, operator, left, right) {
            // TODO: 0 * x = 0; 0 + x = x; 1 * x = x
            (Some(O:: Add | O::Multiply | O::Subtract) | None, O::Multiply, V::Expression(e), E::Binary {left: V::Integer(l), operator: latest_operator@ (O::Add | O::Multiply), right: remainder}) => {
                left = V::Integer(l);
                right = E::Binary {left: V::Expression(e), operator: latest_operator, right: remainder};
                continue;
            }
            (Some(O:: Add | O::Multiply | O::Subtract) | None, O::Multiply, V::Integer(l), E::Binary {left: V::Expression(r), operator: latest_operator@(O::Add | O:: Multiply | O::Divide), right: remainder}) if is_monomial(&r) => {
                left = V::Integer(l);
                operator = O::Multiply;
                right = *r;
                flatten_expression_assuming_precedence_is_correct(&mut right, *remainder, latest_operator);
                continue;
            }
            (None, O::Add, V::Integer(l), E::Binary {left: V::Expression(r), operator: O::Add, right: remainder}) if r.operations().all(|(operator, _)| matches!(operator, O::Add | O::Multiply | O::Divide)) => {
                left = V::Integer(l);
                operator = O::Add;
                right = *r;
                flatten_expression_assuming_precedence_is_correct(&mut right, *remainder, O::Add);
                continue;
            }
            (_, O::Divide, V::Expression(e), r1) => match *e {
                E::Value(v) => {
                    left = *v;
                    right = r1;
                    continue;
                }
                E::Binary {left: l, operator: latest_operator@O::Multiply, right: remainder} if is_monomial(&remainder) && matches!(initial_operator, Some(O::Multiply | O::Add | O::Subtract) | None) => {
                    left = l;
                    operator = latest_operator;
                    right = *remainder;
                    flatten_expression_assuming_precedence_is_correct(&mut right, r1, O::Divide);
                    continue;
                }
                E::Binary { .. } => return Ok(E::Binary {left: V::Expression(e), operator, right: Box::new(r1)}),
            }
            (_, O::Subtract, V::Expression(e), r1) => match *e {
                E::Value(v) => {
                    left = *v;
                    right = r1;
                    continue;
                }
                E::Binary {left: l, operator: latest_operator@(O::Add | O::Multiply | O::Divide), right: remainder} if remainder.operations().all(
                    |(operator, _)| matches!(operator, O::Add | O::Multiply | O::Divide)
                ) && initial_operator.is_none() => {
                    left = l;
                    operator = latest_operator;
                    right = *remainder;
                    continue;
                }
                E::Binary { .. } => return Ok(E::Binary {left: V::Expression(e), operator, right: Box::new(r1)}),
            }
            (Some(O::Subtract), O::Add, V::Expression(e), r1) => match *e {
                E::Value(v) => {
                    left = *v;
                    right = r1;
                    continue;
                }
                E::Binary { .. } => return Ok(E::Binary {left: V::Expression(e), operator, right: Box::new(r1)}),
            }
            // Example: 22u8 - (...)
            (None, O::Subtract, V::Integer(l), E::Value(v)) => match *v {
                // Example: 22u8 - 5u8
                V::Integer(r) => {
                    return Ok(E::Value(Box::new(V::Integer(
                        l.checked_sub(r).ok_or(ConstantFoldingError::Overflow)?,
                    ))))
                }
                // Example: 22u8 - x
                V::Identifier(_) => {
                    return Ok(E::Binary {
                        left: V::Integer(l),
                        operator: O::Subtract,
                        right: Box::new(E::Value(v)),
                    })
                }
                // Example: 22u8 - (...)
                V::Expression(e) => match *e {
                    e @ E::Value(_) => {
                        // remove redundant parentheses
                        left = V::Integer(l);
                        right = e;
                        continue;
                    }
                    r @ E::Binary { .. } => {
                        return Ok(E::Binary {
                            left: V::Integer(l),
                            operator: O::Subtract,
                            right: Box::new(E::Value(Box::new(V::Expression(Box::new(r))))),
                        })
                    }
                },
            },

            // Example: [(..) ±] 22u8 / (..)
            (
                Some(O::Add | O::Subtract) | None,
                O::Divide,
                V::Integer(l),
                E::Value(mut v),
            ) => match *v {
                // Example: [(..) ±] 22u8 / 5u8
                V::Integer(ref mut r) => {
                    *r = l
                        .checked_div(*r)
                        .ok_or(ConstantFoldingError::DivisionByZero)?;
                    return Ok(E::Value(v));
                }
                // Example: [(..) ±] 22u8 / x
                V::Identifier(_) => {
                    return Ok(E::Binary {
                        left: V::Integer(l),
                        operator: O::Divide,
                        right: Box::new(E::Value(v)),
                    });
                }
                // Example: [(..) ±] 22u8 / (...)
                V::Expression(e) => match *e {
                    E::Binary { .. } => {
                        return Ok(E::Binary {
                            left: V::Integer(l),
                            operator: O::Divide,
                            right: Box::new(E::Value(Box::new(V::Expression(e)))),
                        });
                    }
                    E::Value(_) => {
                        // remove redundant parentheses
                        left = V::Integer(l);
                        right = *e;
                        continue;
                    }
                },
            },
            // Example: [(..) ±] 22u8 * 5u8 ±*/ (..)
            (Some(O::Add | O::Subtract) | None, O::Multiply, V::Expression(e0), r1) => {
                match *e0 {
                    E::Value(v0) => {
                        left = *v0;
                        right = r1;
                        continue;
                    }
                    E::Binary {
                        left: l,
                        operator: O::Multiply,
                        right: remainder,
                    } if is_monomial(&remainder) => match r1 {
                        E::Value(v1) => match *v1 {
                            V::Integer(r1) => {
                                left = V::Integer(r1);
                                operator = O::Multiply;
                                right = E::Binary { left: l, operator: O::Multiply, right: remainder };
                                continue;
                            }
                            V::Identifier(_) | V::Expression(_) => {
                                left = l;
                                operator = O::Multiply;
                                right = *remainder;
                                flatten_expression_assuming_precedence_is_correct(&mut right, E::Value(v1), O::Multiply);
                                continue;
                            }
                        }
                        E::Binary { .. } => {
                            left = l;
                            operator = O::Multiply;
                            right = *remainder;
                            // Associativity of multiplication justifies this transformation
                            flatten_expression_assuming_precedence_is_correct(
                                &mut right,
                                r1,
                                O::Multiply,
                            );
                            continue;
                        }
                    }
                    l @ E::Binary { .. } => match r1 {
                        E::Binary {
                            left: r @ V::Integer(_),
                            operator,
                            right: remainder,
                        } => {
                            return Ok(E::Binary {
                                left: r,
                                operator: O::Multiply,
                                right: Box::new(E::Binary {
                                    left: V::Expression(Box::new(l)),
                                    operator,
                                    right: remainder,
                                }),
                            })
                        }
                        r @ E::Binary { .. } => {
                            return Ok(E::Binary {
                                left: V::Expression(Box::new(l)),
                                operator: O::Multiply,
                                right: Box::new(r),
                            })
                        }
                        E::Value(r1) => match *r1 {
                            V::Integer(r1) => {
                                return Ok(E::Binary {
                                    left: V::Integer(r1),
                                    operator: O::Multiply,
                                    right: Box::new(E::Value(Box::new(V::Expression(
                                        Box::new(l),
                                    )))),
                                })
                            }
                            V::Identifier(r) => {
                                return Ok(E::Binary {
                                    left: V::Expression(Box::new(l)),
                                    operator: O::Multiply,
                                    right: Box::new(E::Value(Box::new(V::Identifier(r)))),
                                })
                            }
                            V::Expression(r) => match *r {
                                r @ E::Value(_) => {
                                    left = V::Expression(Box::new(l));
                                    right = r;
                                    continue;
                                }
                                r @ E::Binary { .. } => {
                                    return Ok(E::Binary {
                                        left: V::Expression(Box::new(l)),
                                        operator: O::Multiply,
                                        right: Box::new(E::Value(Box::new(V::Expression(
                                            Box::new(r),
                                        )))),
                                    })
                                }
                            },
                        },
                    },
                }
            }
            // Example: [(..) +] (...) + (...)
            (Some(O::Add) | None, O::Add, V::Expression(e0), E::Value(v1)) => {
                match (*e0, *v1) {
                    // Example: [(..) +] (... ±*/ ...) + 5u8
                    (r @ E::Binary { .. }, l @ V::Integer(_)) => {
                        left = l;
                        right = E::Value(Box::new(V::Expression(Box::new(r))));
                        continue;
                    }
                    // Example: [(..) +] (... ±*/ ...) + x
                    (
                        E::Binary {
                            left: new_left,
                            operator: leftmost_operator,
                            right: remainder,
                        },
                        r @ V::Identifier(_),
                    ) => {
                        left = new_left;
                        operator = leftmost_operator;
                        right = *remainder;
                        flatten_expression_assuming_precedence_is_correct(
                            &mut right,
                            E::Value(Box::new(r)),
                            O::Add,
                        );
                        continue;
                    }
                    // Example: [(..) +] (...) + 22u8
                    (r @ E::Value(_), l @ V::Integer(_)) => {
                        left = l;
                        right = r;
                        continue;
                    }
                    // Example: [(..) +] (...) + x
                    (E::Value(l), r @ V::Identifier(_)) => {
                        left = *l;
                        right = E::Value(Box::new(r));
                        continue;
                    }

                    (E::Binary {left: l, operator: latest_operator@(O::Add | O::Multiply | O::Divide) // Can't include subtraction because this is potentially in an addition context, so left to right ordering would break
                        , right: remainder}, V::Expression(r1)) if remainder.operations().all(|(operator, _)| matches!(operator, O::Add | O::Multiply | O::Subtract)) => {
                        left = l;
                        operator = latest_operator;
                        right = *remainder;
                        flatten_expression_assuming_precedence_is_correct(&mut right, if r1.operations().any(|(operator, _)| matches!(operator, O::Subtract)) {E::Value(Box::new(V::Expression(r1)))} else {*r1}, O::Add);
                        continue;
                    }
                    (l, r ) => return Ok(E::Binary {left: V::Expression(Box::new(l)), operator: O::Add, right: Box::new(E::Value(Box::new(r)))}),

                }
            }
            (Some(O::Add) | None, O::Add, V::Expression(e), E::Binary{left: V::Integer(l), operator: latest_operator@O::Add, right: remainder}) => {
                left = V::Integer(l);
                right = E::Binary {left: V::Expression(e), operator, right: remainder};
                operator = latest_operator;
                continue;
            }

            // Example: [(..) +] (...) + (...)
            (Some(O::Add) | None, O::Add, V::Expression(e0), r1) => match *e0 {
                E::Value(v0) => {
                    left = *v0;
                    right = r1;
                    continue;
                }
                E::Binary {
                    left: l,
                    operator: new_operator,
                    right: remainder,
                } => {
                    left = l;
                    operator = new_operator;
                    right = *remainder;
                    flatten_expression_assuming_precedence_is_correct(
                        &mut right,
                        r1,
                        O::Add,
                    )
                }
            }, // TODO: review this case. This should be similar to the multiplication case with less conditions
            // Example: [(..) *] (...) * (...)
            (Some(O::Multiply), O::Multiply, V::Expression(e0), r1) => match *e0 {
                // Example: [(..) *] (...) * 5u8
                E::Value(v0) => {
                    left = *v0;
                    right = r1;
                    continue;
                }
                // Example: [(..) *] (... * ...) * (...)
                E::Binary {
                    left: l,
                    operator: O::Multiply,
                    right: remainder,
                } if is_monomial(&remainder) => {
                    left = l;
                    operator = O::Multiply;
                    right = *remainder;
                    flatten_expression_assuming_precedence_is_correct(
                        &mut right,
                        r1,
                        O::Multiply,
                    );

                    continue;
                }
                // Example: [(..) *] (...) * (...)
                E::Binary { .. } => match r1 {
                    E::Binary {
                        left: l @ V::Integer(_), operator: latest_operator, right: remainder
                    } => {
                        left = l;
                        operator = O::Multiply;
                        right = E::Binary {
                            left: V::Expression(e0),
                            operator: latest_operator,
                            right: remainder
                        };
                    }
                    E::Binary { .. } => return Ok(E::Binary { left: V::Expression(e0), operator: O::Multiply, right: Box::new(r1) }),
                    E::Value(r1) => match *r1 {
                        V::Integer(r1) => {
                            left = V::Integer(r1);
                            right = E::Value(Box::new(V::Expression(e0)));
                            continue;
                        }
                        V::Identifier(r1) => {
                            left = V::Expression(e0);
                            right = E::Value(Box::new(V::Identifier(r1)));
                            continue;
                        }
                        V::Expression(r1) if is_monomial(&r1) => {
                            left = V::Expression(r1);
                            right = E::Value(Box::new(V::Expression(e0)));
                        }
                        V::Expression(r1) => return Ok(E::Binary { left: V::Expression(e0), operator: O::Multiply, right: Box::new(E::Value(Box::new(V::Expression(r1)))) })
                    }
                }
            },
            // Example: (..) * (...) + (...)
            (Some(O::Multiply), O::Add, V::Expression(e0), r1) => match *e0 {
                E::Value(v0) => {
                    left = *v0;
                    right = r1;
                    continue;
                }
                E::Binary {
                    left: l,
                    operator: O::Multiply,
                    right: remainder,
                } if is_monomial(&remainder) => {
                    left = l;
                    operator = O::Multiply;
                    right = *remainder;
                    flatten_expression_assuming_precedence_is_correct(
                        &mut right,
                        r1,
                        O::Add,
                    );
                    continue;
                }
                l @ E::Binary { .. } => {
                    return Ok(E::Binary {
                        left: V::Expression(Box::new(l)),
                        operator: O::Add,
                        right: Box::new(r1),
                    })
                }
            },
            (
                Some(O::Multiply),
                O::Multiply,
                r @ V::Identifier(_),
                E::Binary {
                    left: l @ V::Integer(_),
                    operator: latest_operator@O::Add,
                    right: remainder,
                },
            ) | // Example: [(...) +] x + 2u8 + (...)
            (
                Some(O::Add) | None,
                O::Add,
                r @ V::Identifier(_),
                E::Binary {
                    left: l @ V::Integer(_),
                    operator: latest_operator@O::Add,
                    right: remainder,
                },
            ) => {
                // apply commutativity of multiplication/addition
                // This is inside a multiplication where there is an identifier before the addition operator that terminates the multiplication grouping
                // Identifiers should be pushed to the right within products, so that all the constant coefficients can be multiplied together to reduce runtime operations
                // apply commutativity of addition
                // This is inside an addition where there is an identifier before the addition operator
                // that terminates the addition grouping
                // Identifiers should be pushed to the right within sums, so that all the constant
                // coefficients can be added together to reduce runtime operations
                return Ok(E::Binary {
                    left: l,
                    operator,
                    right: Box::new(E::Binary {
                        left: r,
                        operator: latest_operator,
                        right: remainder,
                    }),
                });
            }

            // Example: (..) * 2u8 * 3u8 + (...)
            (
                Some(O::Multiply),
                O::Multiply,
                V::Integer(l),
                E::Binary {
                    left: V::Integer(r),
                    operator: O::Add,
                    right: remainder,
                },
            ) => {
                return Ok(E::Binary {
                    left: V::Integer(
                        l.checked_mul(r).ok_or(ConstantFoldingError::Overflow)?,
                    ),
                    operator: O::Add,
                    right: remainder,
                })
            }



            // [(..) +] x + (...)
            (Some(O::Add) | None, O::Add, r @ V::Identifier(_), E::Value(v)) => match *v {
                // [(..) +] x + 5u8
                V::Integer(l) => {
                    // println!("Swapping {}, {}", r, l);
                    // apply commutativity of addition
                    return Ok(E::Binary {
                        left: V::Integer(l),
                        operator: O::Add,
                        right: Box::new(E::Value(Box::new(r))),
                    });
                }
                // [(..) +] x + y
                r1 @ V::Identifier(_) => {
                    return Ok(E::Binary {
                        left: r,
                        operator: O::Add,
                        right: Box::new(E::Value(Box::new(r1))),
                    })
                }
                // [(..) +] x + (... + ... * ...)
                V::Expression(e)
                if e.operations()
                    .all(|(operator, _)| matches!(operator, O::Add | O::Multiply)) =>
                    {
                        left = r;
                        right = *e;
                        // Treat the parenthesized expression as an unparenthesized and continue reducing
                        // This is safe because of plus's precedence
                        continue;
                    }
                // [(..) +] x + (...)
                V::Expression(e) => match *e {
                    E::Value(_) => {
                        left = r;
                        right = *e;
                    }
                    E::Binary { .. } => {
                        return Ok(E::Binary {
                            left: V::Expression(e),
                            operator: O::Add,
                            right: Box::new(E::Value(Box::new(r))),
                        })
                    }
                },
            }, // Box patterns would be nice here, but they are nightly feature unfortunately
            // Example: [(...) +] 5u8 * 2u8 +* (...)
            (
                Some(O::Add) | None,
                O::Multiply,
                V::Integer(l),
                E::Binary {
                    left: V::Integer(r),
                    operator: latest_operator @ (O::Add | O::Multiply),
                    right: remainder,
                },
            ) | (Some(O::Add | O::Subtract) | None, O::Multiply, V::Integer(l), E::Binary { left: V::Integer(r), operator: latest_operator @ (O::Add | O::Subtract | O::Multiply | O::Divide), right: remainder })
            | // Example: (...) + 6u8 + 3u8 ± (...)
            (
                Some(O::Add) | None,
                O::Add,
                V::Integer(l),
                E::Binary {
                    left: V::Integer(r),
                    operator: latest_operator @ (O::Add | O::Subtract), // multiply and division can't go here because those multiplications and divisions must be done first due to precedence
                    right: remainder,
                },
            ) | // Example: (...) * 2u8 * 3u8 * (...) +
            (
                Some(O::Multiply),
                O::Multiply,
                V::Integer(l),
                E::Binary {
                    left: V::Integer(r),
                    operator: latest_operator@O::Multiply,
                    right: remainder,
                },
            ) | // Example: [(..) ±] 22u8 / 5u8 ±*/ (..)
            (
                Some(O::Add | O::Subtract) | None,
                O::Divide,
                V::Integer(l),
                E::Binary {
                    left: V::Integer(r),
                    operator: latest_operator,
                    right: remainder,
                },
            ) | (None, O::Subtract, V::Integer(l), E::Binary { left: V::Integer(r), operator: latest_operator @ (O::Add | O::Subtract), right: remainder })
            => {
                left = V::Integer(operator.fold_constants(l, r)?);
                operator = latest_operator;
                right = *remainder;
                continue;
            }
            // Example: [(...) +] x * (...)
            (Some(O::Add) | None, O::Multiply, l @ V::Identifier(_), E::Value(e)) => {
                match *e {
                    r @ V::Integer(_) => {
                        return Ok(E::Binary {
                            left: r,
                            operator: O::Multiply,
                            right: Box::new(E::Value(Box::new(l))),
                        });
                    }
                    r @ V::Identifier(_) => {
                        return Ok(E::Binary {
                            left: l,
                            operator: O::Multiply,
                            right: Box::new(E::Value(Box::new(r))),
                        })
                    }
                    V::Expression(e) => match *e {
                        e @ E::Value(_) => {
                            left = l;
                            right = e;
                            continue;
                        }
                        E::Binary {
                            operator: O::Multiply,
                            right: ref remainder,
                            ..
                        } if is_monomial(remainder) =>
                            {
                                left = l;
                                right = *e;
                                continue;
                            }
                        E::Binary { .. } => {
                            return Ok(E::Binary {
                                left: V::Expression(e),
                                operator: O::Multiply,
                                right: Box::new(E::Value(Box::new(l))),
                            })
                        }
                    },
                }
            }


            // Example: (...) + 1u8 + (...)
            (Some(O::Add) | None, O::Add, V::Integer(ref l), E::Value(v)) => match *v {
                // Example: (...) + 1u8 + 2u8
                V::Integer(r) => {
                    return Ok(E::Value(Box::new(V::Integer(
                        l.checked_add(r).ok_or(ConstantFoldingError::Overflow)?,
                    ))))
                }
                // Example: (...) + 1u8 + x
                V::Identifier(identifier) => {
                    return Ok(E::Binary {
                        left: V::Integer(*l),
                        operator: O::Add,
                        right: Box::new(E::Value(Box::new(V::Identifier(identifier)))),
                    })
                }
                // Example: (...) + 1u8 + (...)
                V::Expression(e) if e.operations().all(|(operator, _)| matches!(operator, O::Multiply | O::Add | O::Divide))=> {
                    left = V::Integer(*l);
                    right = *e;
                    // TODO:  is this correct with subtraction
                    continue;
                }
                V::Expression(e) => {
                    return Ok(E::Binary {
                        left: V::Integer(*l),
                        operator: O::Add,
                        right: Box::new(E::Value(Box::new(V::Expression(e)))),
                    })
                }
            },
            // Example: (...) + 2u8 * (...)
            (
                Some(O::Add | O::Subtract) | None,
                O::Multiply,
                V::Integer(ref l),
                E::Value(v),
            ) => {
                match *v {
                    // Example: (...) + 2u8 * 2u8
                    V::Integer(r) => {
                        return Ok(E::Value(Box::new(V::Integer(
                            l.checked_mul(r).ok_or(ConstantFoldingError::Overflow)?,
                        ))))
                    }
                    // Example: (...) + 2u8 * x
                    V::Identifier(identifier) => {
                        return Ok(E::Binary {
                            left: V::Integer(*l),
                            operator: O::Multiply,
                            right: Box::new(E::Value(Box::new(V::Identifier(identifier)))),
                        })
                    }
                    // Example: (...) + 2u8 * (...)
                    V::Expression(e)
                    if e.operations().any(|(operator, _)| {
                        matches!(
                                        operator,
                                        O::Add | O::Subtract // Addition and subtraction are excluded because then distributive law would be required to allow reducing further with question benefits in terms of number of operations.
                            | O::Divide // exclude division because having a division might reduce a value so that it doesn't overflow when multiplied
                                    )
                    }) =>
                        {
                            return Ok(E::Binary {
                                left: V::Integer(*l),
                                operator: O::Multiply,
                                right: Box::new(E::Value(Box::new(V::Expression(e)))),
                            })
                        }
                    // Example: (...) + 2u8 * (... * ... * ...)
                    V::Expression(e) => {
                        // Guaranteed to only have integer multiplications
                        left = V::Integer(*l);
                        right = *e;
                        continue;
                    }
                }
            }
            // Example: (...) * x * (..)
            (Some(O::Multiply), O::Multiply, r @ V::Identifier(_), E::Value(v)) => match *v
            {
                // Example: (...) * x * 2u8
                V::Integer(l) => {
                    return Ok(E::Binary {
                        left: V::Integer(l),
                        operator: O::Multiply,
                        right: Box::new(E::Value(Box::new(r))),
                    })
                }
                // Example: (...) * x * y
                V::Identifier(_) => {
                    return Ok(E::Binary {
                        left: r,
                        operator: O::Multiply,
                        right: Box::new(E::Value(v)),
                    })
                }
                // Example: (...) * x * (...)
                V::Expression(e) => match *e {
                    E::Value(_) => {
                        left = r;
                        right = *e;
                        continue;
                    }
                    // E::Binary {operator: O::Multiply, right: ref remainder, ..} if is_monomial(&remainder) => {
                    //     left = r;
                    //     right = *e;
                    //     continue;
                    // }
                    E::Binary { .. } => {
                        return Ok(E::Binary {
                            left: V::Expression(e),
                            operator: O::Multiply,
                            right: Box::new(E::Value(Box::new(r))),
                        })
                    }
                },
            },
            // Example: (...) * 3u8 * (...)
            (Some(O::Multiply), O::Multiply, V::Integer(ref l), E::Value(v)) => match *v {
                // Example: * 3u8 * 2u8
                V::Integer(r) => {
                    return Ok(E::Value(Box::new(V::Integer(
                        l.checked_mul(r).ok_or(ConstantFoldingError::Overflow)?,
                    ))))
                }
                // Example:(...) * 3u8 * x
                V::Identifier(identifier) => {
                    return Ok(E::Binary {
                        left: V::Integer(*l),
                        operator: O::Multiply,
                        right: Box::new(E::Value(Box::new(V::Identifier(identifier)))),
                    })
                }
                // Example: (...) * 3u8 * (...)
                V::Expression(e)
                if e.operations().any(|(operator, _)| {
                    matches!(
                                    operator,
                                    O::Add | O::Subtract // Addition and subtraction are excluded because then distributive law would be required to allow reducing further with question benefits in terms of number of operations.
                            | O::Divide // exclude division because having a division might reduce a value so that it doesn't overflow when multiplied
                                )
                }) =>
                    {
                        return Ok(E::Binary {
                            left: V::Integer(*l),
                            operator: O::Multiply,
                            right: Box::new(E::Value(Box::new(V::Expression(e)))),
                        })
                    }
                // Example: (...) * 3u8 * (... * ... * ...)
                V::Expression(e) => {
                    left = V::Integer(*l);
                    right = *e;
                    continue;
                }
            },
            // Example: [(...) +] x - (..)
            (
                Some(O::Add) | None,
                operator @ O::Subtract,
                l @ V::Identifier(_),
                E::Value(v),
            )
            // Example: (...) / (..) * (..)
            | (Some(O::Divide), operator @ O::Multiply, l, E::Value(v)) => match *v {
                V::Integer(r) => {
                    return Ok(E::Binary {
                        left: l,
                        operator,
                        right: Box::new(E::Value(Box::new(V::Integer(r)))),
                    })
                }
                V::Identifier(r) => {
                    return Ok(E::Binary {
                        left: l,
                        operator,
                        right: Box::new(E::Value(Box::new(V::Identifier(r)))),
                    })
                }
                V::Expression(e) => match *e {
                    E::Value(_) => {
                        left = l;
                        right = *e;
                        continue;
                    }
                    E::Binary { .. } => {
                        return Ok(E::Binary {
                            left: l,
                            operator,
                            right: Box::new(E::Value(Box::new(V::Expression(e)))),
                        })
                    }
                },
            },
            // Example [(..) ±] z + (..) * (..)
            // Example: [(..) ±] z + (..) / (..)
            (
                Some(O::Add | O::Subtract) | None,
                operator @ O::Add,
                l @ V::Identifier(_),
                r @ E::Binary {
                    operator: O::Multiply | O::Divide,
                    ..
                },
            )
            // Example: 2u8 * x * (..)
            | (
                None,
                operator @ O::Multiply,
                l @ V::Integer(_),
                r @ E::Binary {
                    left: V::Identifier(_),
                    operator: O::Multiply,
                    ..
                },
            ) | (Some(O::Multiply), operator @ O::Divide, l @ V::Integer(_), r @ E::Value(_))
            | (Some(O::Subtract), operator @ O::Add, l @ V::Integer(_), r @ E::Value(_))
            | (Some(O::Divide), operator @ O::Add, l @ V::Integer(_), r @ E::Value(_))
            | (Some(O::Multiply), operator @ O::Subtract, l @ V::Integer(_), r @ E::Value(_))
            | (Some(O::Add), operator @ O::Subtract, l @ V::Integer(_), r @ E::Value(_))
            | (Some(O::Multiply), operator @ O::Add, l, r)
            | // Example: (..) * 2u8 * x + (..)
            (
                Some(O::Multiply),
                operator@O::Multiply,
                l @ V::Integer(_),
                r @ E::Binary {
                    left: V::Identifier(_),
                    operator: O::Add,
                    ..
                },
            ) | (
                Some(O::Add) | None,
                operator@O::Add,
                l @ V::Integer(_),
                r @ E::Binary {
                    operator: O::Multiply,
                    ..
                },
            ) | (
                None,
                operator@O::Multiply,
                l @ V::Integer(_),
                r @ E::Binary {
                    left: V::Identifier(_),
                    operator: O::Add,
                    ..
                },
            ) | (Some(O::Subtract), operator@O::Subtract, l@V::Identifier(_), r@E::Value(_))
            | (None, operator@O::Subtract, l@V::Integer(_), r@E::Binary { left: V::Identifier(_), operator: O::Add | O::Subtract, .. })
            | (Some(O::Divide), operator@O::Divide, l@V::Identifier(_), r@E::Value(_))
            | (None | Some(O::Add | O::Subtract), operator@O::Divide, l@V::Integer(_), r@E::Binary { left: V::Identifier(_), operator: O::Add | O::Subtract | O::Multiply | O::Divide, .. })
            | (None, operator@O::Add, l@V::Integer(_), r@E::Binary { left: V::Identifier(_), operator: O::Add | O::Subtract, .. })
            | (Some(O::Divide), operator@O::Add, l, r)
            | (Some(O::Multiply), operator@O::Divide, l, r)
            | (_, operator, l, r) // catch all remove when testing
            => {
                return Ok(E::Binary {
                    left: l,
                    operator,
                    right: Box::new(r),
                })
            }
            // x => todo!("{:?}", x),   // testing panic: uncomment when testing
        }
    }
}

/// Checks whether a given expression is a monomial, meaning it consists solely of multiplications.
///
/// This function analyzes a binary expression to determine if all operations within it are multiplication.
/// A monomial is an algebraic expression made up of only multiplication operations, with no addition,
/// subtraction, or division. This is useful when optimizing expressions during constant folding, as
/// monomials can often be simplified or factored out more easily.
///
/// # Parameters
///
/// - `remainder`: A reference to the `Expression` to be checked. This expression may contain multiple
///   operations that will be analyzed.
///
/// # Returns
///
/// A `bool` indicating whether the expression is a monomial:
/// - `true` if all operations in the expression are multiplication (`*`).
/// - `false` if any operation in the expression is not multiplication.
///
/// # Note
///
/// - This function relies on the `operations()` method of the `Expression` type to iterate through the
///   operations in the expression. It uses pattern matching to verify that each operation is a multiplication.
fn is_monomial(remainder: &Expression) -> bool {
    use Operator as O;
    remainder
        .operations()
        .all(|(operator, _)| matches!(operator, O::Multiply))
}

/// Flattens an expression by appending a new expression (`r1`) to the rightmost position, assuming operator precedence is already correct.
///
/// This function navigates through the rightmost chain of binary operations in the provided expression
/// and appends a new binary operation with the `final_operator` to the end. It is used when the
/// precedence of operators is assumed to be correct, ensuring that the expression structure remains valid.
///
/// # Parameters
///
/// - `right`: A mutable reference to the `Expression` that will be flattened.
/// - `r1`: The new `Expression` to be appended to the rightmost position.
/// - `final_operator`: The operator to be used in the new binary operation that will combine `right` and `r1`.
///
/// # Note
///
/// - This function assumes that the operator precedence is already correct, so it does not attempt to re-balance or re-order the expression tree.
/// - The function uses a loop to traverse to the rightmost part of the expression, where the new operation is appended.
fn flatten_expression_assuming_precedence_is_correct(
    right: &mut Expression,

    r1: Expression,
    final_operator: Operator,
) {
    use Expression as E;
    use Value as V;

    let mut remainder = right;
    while let E::Binary { right: end, .. } = remainder {
        // TODO:  consider merging this loop with the check for multiplications to reduce passes
        remainder = &mut **end;
        // TODO: consider doing some reductions in this loop
    }
    match remainder {
        E::Value(v) => {
            *remainder = E::Binary {
                left: std::mem::replace(&mut **v, V::Integer(0)), // TODO: this is a hack
                operator: final_operator,
                right: Box::new(r1),
            };
        }
        E::Binary { .. } => {
            unreachable!("All binary cases should have been handled")
        }
    }
}

/// Performs constant folding on a `Value`, optimizing it by evaluating constants at compile time using the provided symbol table.
///
/// This function processes a `Value` by folding constants and simplifying expressions where possible.
/// If the value is an integer, it is returned as-is. If it is an identifier, the function checks the symbol
/// table for a known value and replaces the identifier with that value if available. If the value is an expression,
/// the function attempts to fold constants within that expression and returns the optimized result.
///
/// # Parameters
///
/// - `value`: The `Value` to be processed for constant folding. This can be an integer, identifier, or expression.
/// - `symbols`: A reference to the `SymbolTable` that holds known variable values. This table is used to resolve
///   identifiers to their constant values, if available.
///
/// # Returns
///
/// A `Result<Value, ConstantFoldingError>`:
/// - `Ok(Value)` containing the optimized value if the folding is successful.
/// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow or division by zero.
fn value_constant_folding(
    value: Value,
    symbols: &SymbolTable,
) -> Result<Value, ConstantFoldingError> {
    use Expression as E;
    use Value as V;
    match value {
        V::Integer(i) => Ok(V::Integer(i)),
        V::Identifier(identifier) => {
            if let Some(value) = symbols.get(&identifier) {
                Ok(V::Integer(*value))
            } else {
                Ok(V::Identifier(identifier))
            }
        }
        V::Expression(expression) => {
            let expression = expression_constant_folding(*expression, symbols, None)?;
            match expression {
                E::Value(v) => Ok(*v),
                E::Binary { .. } => Ok(V::Expression(Box::new(expression))),
            }
        }
    }
}

impl Value {
    /// Performs constant folding on a `Value` by delegating the task to the `value_constant_folding` function.
    ///
    /// This function acts as a wrapper around the `value_constant_folding` function, passing the `Value`
    /// and the symbol table to it for constant folding. The purpose is to simplify the interface by directly
    /// invoking the folding process on the `Value` instance.
    ///
    /// # Parameters
    ///
    /// - `self`: The `Value` instance to be processed for constant folding.
    /// - `symbols`: A reference to the `SymbolTable` that holds known variable values. This table is used
    ///   to resolve identifiers to their constant values, if available.
    ///
    /// # Returns
    ///
    /// A `Result<Value, ConstantFoldingError>`:
    /// - `Ok(Value)` containing the optimized value if the folding is successful.
    /// - `Err(ConstantFoldingError)` if an error occurs during the folding process, such as an overflow or division by zero.
    pub fn constant_folding(self, symbols: &SymbolTable) -> Result<Value, ConstantFoldingError> {
        value_constant_folding(self, symbols)
    }
}

// Test cases for private functions
#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use std::fs;
    use Expression as E;
    use Operator as O;
    use Value as V;

    // Parse before.leo and generate the AST after running constant folding. Then, check against the canned results in after.leo
    #[test]
    fn test_constant_folding_and_parsing() {
        let unparsed_file = fs::read_to_string("src/files/before.leo").expect("cannot read file");
        let file = parse(&unparsed_file).expect("unsuccessful parse");
        let file = file
            .constant_folding()
            .expect("unsuccessful constant folding");
        let expected_file = fs::read_to_string("src/files/after.leo").expect("cannot read file");
        let expected_file =
            parse(&expected_file).expect("unsuccessful parse of expected after.leo");
        assert_eq!(file, expected_file);
    }

    #[test]
    fn test_constant_folding_with_inputs_and_parsing() {
        let unparsed_file =
            fs::read_to_string("src/files/before_with_input.leo").expect("cannot read file");
        let file = parse(&unparsed_file).expect("unsuccessful parse");
        let file = file
            .constant_folding()
            .expect("unsuccessful constant folding");
        let expected_file =
            fs::read_to_string("src/files/after_with_input.leo").expect("cannot read file");
        let expected_file =
            parse(&expected_file).expect("unsuccessful parse of expected after.leo");
        assert_eq!(file.statements, expected_file.statements);
        println!("{}", file);
    }

    // x where x = 5
    #[test]
    fn test_constant_folding() {
        let mut symbols = SymbolTable::new();
        symbols.insert("x".to_string(), 5);
        let value = V::Identifier("x".to_string());
        let value = value_constant_folding(value, &symbols);
        assert_eq!(value, Ok(V::Integer(5)));
    }

    // Example: x + 5 where x = 5
    #[test]
    fn test_constant_folding_expression() {
        let mut symbols = SymbolTable::new();
        symbols.insert("x".to_string(), 5);
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: Operator::Add,
            right: Box::new(E::Value(Box::new(V::Integer(5)))),
        };
        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(10)))));
    }

    // Example: 5 * 5
    #[test]
    fn test_constant_folding_expression_multiply() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(5),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Integer(5)))),
        };
        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(25)))));
    }

    // Example: (5 + 7) * x where x = 2
    #[test]
    fn test_constant_folding_expression_add() {
        let symbols = SymbolTable::from([("x".to_string(), 2)]);
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Integer(5),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(7)))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(24)))));
    }

    // Example: x * (y + 2) where x = 3 and y = 4
    #[test]
    fn test_constant_folding_multiply_with_addition() {
        let symbols = SymbolTable::from([("x".to_string(), 3), ("y".to_string(), 4)]);
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Identifier("y".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(2)))),
            }))))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(18)))));
    }

    // Example: (x + 1) * (y - 1) where x = 2 and y = 3
    #[test]
    fn test_constant_folding_multiply_with_subtraction() {
        let symbols = SymbolTable::from([("x".to_string(), 2), ("y".to_string(), 3)]);
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(1)))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Identifier("y".to_string()),
                operator: O::Subtract,
                right: Box::new(E::Value(Box::new(V::Integer(1)))),
            }))))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(6)))));
    }

    // Example: x + (y * z) where x = 5, y = 3, z = 4
    #[test]
    fn test_constant_folding_add_with_multiplication() {
        let symbols = SymbolTable::from([
            ("x".to_string(), 5),
            ("y".to_string(), 3),
            ("z".to_string(), 4),
        ]);
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Add,
            right: Box::new(E::Binary {
                left: V::Identifier("y".to_string()),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Integer(4)))),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(17)))));
    }

    // Example: (x - y) * z where x = 10, y = 3, z = 2
    #[test]
    fn test_constant_folding_subtract_with_multiplication() {
        let symbols = SymbolTable::from([
            ("x".to_string(), 10),
            ("y".to_string(), 3),
            ("z".to_string(), 2),
        ]);
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Subtract,
                right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Identifier("z".to_string())))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(14)))));
    }

    // Example: x / y where x = 10 and y = 2
    #[test]
    fn test_constant_folding_division() {
        let symbols = SymbolTable::from([("x".to_string(), 10), ("y".to_string(), 2)]);
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(5)))));
    }

    // Example: x / 0 where x = 10 (should return a DivisionByZero error)
    #[test]
    fn test_constant_folding_division_by_zero() {
        let symbols = SymbolTable::from([("x".to_string(), 10)]);
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Integer(0)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::DivisionByZero));
    }

    // Example: (x + y) * z where x = 1, y = 2, z = 3
    #[test]
    fn test_constant_folding_addition_with_multiplication() {
        let symbols = SymbolTable::from([
            ("x".to_string(), 1),
            ("y".to_string(), 2),
            ("z".to_string(), 3),
        ]);
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Identifier("z".to_string())))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(9)))));
    }

    // Example: 250 + 10 (should return an Overflow error)
    #[test]
    fn test_constant_folding_addition_overflow() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(250),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Integer(10)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: 20 * 15 (should return an Overflow error)
    #[test]
    fn test_constant_folding_multiplication_overflow() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(20),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Integer(15)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: 255 + 1 (should return an Overflow error)
    #[test]
    fn test_constant_folding_max_addition_overflow() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(255),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Integer(1)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: 16 * 16 (should return an Overflow error)
    #[test]
    fn test_constant_folding_max_multiplication_overflow() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(16),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Integer(16)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: (x + 3) * 128 where x = 2 (should return an Overflow error)
    #[test]
    fn test_constant_folding_addition_and_multiplication_overflow() {
        let symbols = SymbolTable::from([("x".to_string(), 2)]);
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(3)))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Integer(128)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: (x + 3) + 5 where x is not defined (partial folding, should fold to x + 8)
    #[test]
    fn test_partial_constant_folding_addition_with_undefined_variable() {
        let symbols = SymbolTable::new(); // x is not defined in the symbol table
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(3)))),
            })),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Integer(5)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Integer(8),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            })
        );
    }

    // Example: (x * 2) + 4 where x is not defined (partial folding, should fold to x * 2 + 4)
    #[test]
    fn test_partial_constant_folding_multiplication_with_undefined_variable() {
        let symbols = SymbolTable::new(); // x is not defined in the symbol table
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Integer(2)))),
            })),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Integer(4)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Integer(4),
                operator: O::Add,
                right: Box::new(E::Binary {
                    left: V::Integer(2),
                    operator: O::Multiply,
                    right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
                }),
            })
        );
    }

    // Example: x + y where neither x nor y are defined (no folding impact, should remain as is)
    #[test]
    fn test_no_folding_impact_with_undefined_variables() {
        let symbols = SymbolTable::new(); // Neither x nor y are defined in the symbol table
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
            })
        );
    }
    // Example: 2 * 3 + x
    #[test]
    fn test_constant_folding_multiplication_precedence() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(2),
            operator: O::Multiply,
            right: Box::new(E::Binary {
                left: V::Integer(3),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Integer(6),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            })
        );
    }

    // Addition with Identifiers
    #[test]
    fn test_constant_folding_addition_with_identifiers() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(1),
            operator: O::Add,
            right: Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(2)))),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Integer(3),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            })
        );
    }

    // Multiplication Grouping
    #[test]
    fn test_constant_folding_multiplication_grouping() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(2),
            operator: O::Multiply,
            right: Box::new(E::Binary {
                left: V::Integer(3),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Integer(4)))),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, Some(O::Multiply));
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(24)))));
    }

    // Multiplication and Addition with Identifiers
    #[test]
    fn test_constant_folding_multiplication_and_addition_with_identifiers() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(2),
            operator: O::Multiply,
            right: Box::new(E::Binary {
                left: V::Integer(3),
                operator: O::Multiply,
                right: Box::new(E::Binary {
                    left: V::Identifier("x".to_string()),
                    operator: O::Add,
                    right: Box::new(E::Value(Box::new(V::Integer(4)))),
                }),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: V::Integer(6),
                operator: O::Multiply,
                right: Box::new(E::Binary {
                    left: V::Identifier("x".to_string()),
                    operator: O::Add,
                    right: Box::new(E::Value(Box::new(V::Integer(4)))),
                })
            })
        );
    }

    // Handling Parenthesized Expressions in Addition
    #[test]
    fn test_constant_folding_parenthesized_expression_in_addition() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Identifier("y".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(1)))),
            }))))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(
            expression,
            Ok(E::Binary {
                left: (V::Integer(1)),
                operator: O::Add,
                right: Box::new(E::Binary {
                    left: V::Identifier("x".to_string()),
                    operator: O::Add,
                    right: Box::new(E::Value(Box::new(V::Identifier("y".to_string())))),
                })
            })
        );
    }

    // Overflow Handling in Multiplication
    #[test]
    fn test_constant_folding_multiplication_overflow_handling() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(200),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Integer(200)))),
        };

        let expression = expression_constant_folding(expression, &symbols, Some(O::Multiply));
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Nested Expressions with Mixed Operators
    // Example: (1 + 2) * (4 + 5)
    #[test]
    fn test_constant_folding_nested_expressions_with_mixed_operators() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Integer(1),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(2)))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Integer(4),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(5)))),
            }))))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(27)))));
    }

    // Complex Expression Folding
    // Example: (2 + 3) * (4 + 5) + 6
    #[test]
    fn test_constant_folding_complex_expression() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Integer(2),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(3)))),
            })),
            operator: O::Multiply,
            right: Box::new(E::Binary {
                left: V::Expression(Box::new(E::Binary {
                    left: V::Integer(4),
                    operator: O::Add,
                    right: Box::new(E::Value(Box::new(V::Integer(5)))),
                })),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(6)))),
            }),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Ok(E::Value(Box::new(V::Integer(51)))));
    }

    // Negative Overflow Handling in Subtraction
    #[test]
    fn test_constant_folding_subtraction_negative_overflow() {
        let symbols = SymbolTable::new();
        let expression = E::Binary {
            left: V::Integer(5),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Integer(10)))),
        };

        let expression = expression_constant_folding(expression, &symbols, None);
        assert_eq!(expression, Err(ConstantFoldingError::Overflow));
    }

    // Example: 255 - (128 - x)
    #[test]
    fn test_constant_folding_subtraction_with_nested_expression() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Integer(128),
                operator: O::Subtract,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }))))),
        };

        let folded_expression =
            expression_constant_folding(original_expression.clone(), &symbols, None)
                .expect("Failed to fold expression");
        assert_eq!(original_expression, folded_expression);
    }

    // Example: 255 - ((128 - x))
    // Folded expression should be: 255 - (128 - x)
    #[test]
    fn test_constant_folding_subtraction_with_nested_expression_parenthesized() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Value(
                Box::new(V::Expression(Box::new(E::Binary {
                    left: V::Integer(128),
                    operator: O::Subtract,
                    right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
                }))),
            )))))),
        };

        let folded_expression =
            expression_constant_folding(original_expression.clone(), &symbols, None)
                .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Integer(128),
                operator: O::Subtract,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }))))),
        };
        assert_eq!(folded_expression, expected_expression);
    }

    // Example: ((x + 33) + 33) + 33
    // Folded expression should be: x + 99
    #[test]
    fn test_constant_folding_nested_expression_with_addition() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Expression(Box::new(E::Binary {
                left: V::Expression(Box::new(E::Binary {
                    left: V::Identifier("x".to_string()),
                    operator: O::Add,
                    right: Box::new(E::Value(Box::new(V::Integer(33)))),
                })),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(33)))),
            })),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Integer(33)))),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Integer(99),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
        };
        assert_eq!(folded_expression, expected_expression);
    }

    // Example: x - 6 / 3
    // Folded expression should be: x - 2
    #[test]
    fn test_constant_folding_subtraction_with_division() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Subtract,
            right: Box::new(E::Binary {
                left: V::Integer(6),
                operator: O::Divide,
                right: Box::new(E::Value(Box::new(V::Integer(3)))),
            }),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Integer(2)))),
        };
        assert_eq!(folded_expression, expected_expression);
    }

    //  Example: x - 4 / 2 * 3
    // Folded expression should be: x - 6
    #[test]
    fn test_constant_folding_subtraction_with_multiplication_and_division() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Subtract,
            right: Box::new(E::Binary {
                left: V::Integer(4),
                operator: O::Divide,
                right: Box::new(E::Binary {
                    left: V::Integer(2),
                    operator: O::Multiply,
                    right: Box::new(E::Value(Box::new(V::Integer(3)))),
                }),
            }),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Subtract,
            right: Box::new(E::Value(Box::new(V::Integer(6)))),
        };
        assert_eq!(folded_expression, expected_expression);
    }

    // Example: x + 2 * x
    // Folded expression should be: x + 2 * x
    #[test]
    fn test_constant_folding_addition_with_multiplication_on_the_right() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Identifier("x".to_string()),
            operator: O::Add,
            right: Box::new(E::Binary {
                left: V::Integer(2),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }),
        };

        let folded_expression =
            expression_constant_folding(original_expression.clone(), &symbols, None)
                .expect("Failed to fold expression");

        assert_eq!(folded_expression, original_expression);
    }

    // Example: 255/(x)
    // Folded expression should be: 255/x
    #[test]
    fn test_constant_folding_division_with_identifier() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Value(
                Box::new(V::Identifier("x".to_string())),
            )))))),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
        };
        assert_eq!(folded_expression, expected_expression);
    }

    // Example: 255/(x + 1)
    // Folded expression should be: 255/(1 + x)
    #[test]
    fn test_constant_folding_division_with_addition() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Identifier("x".to_string()),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Integer(1)))),
            }))))),
        };

        let expected_expression = E::Binary {
            left: V::Integer(255),
            operator: O::Divide,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Integer(1),
                operator: O::Add,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }))))),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        assert_eq!(folded_expression, expected_expression);
    }

    // Example:  1 + (x * 2) * 2
    // Folded expression should be: 1 + x * 4
    #[test]
    fn test_constant_folding_addition_with_multiplication_on_the_right_nested() {
        let symbols = SymbolTable::new();
        let original_expression = E::Binary {
            left: V::Integer(1),
            operator: O::Add,
            right: Box::new(E::Value(Box::new(V::Expression(Box::new(E::Binary {
                left: V::Expression(Box::new(E::Binary {
                    left: V::Identifier("x".to_string()),
                    operator: O::Multiply,
                    right: Box::new(E::Value(Box::new(V::Integer(2)))),
                })),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Integer(2)))),
            }))))),
        };

        let folded_expression = expression_constant_folding(original_expression, &symbols, None)
            .expect("Failed to fold expression");

        let expected_expression = E::Binary {
            left: V::Integer(1),
            operator: O::Add,
            right: Box::new(E::Binary {
                left: V::Integer(4),
                operator: O::Multiply,
                right: Box::new(E::Value(Box::new(V::Identifier("x".to_string())))),
            }),
        };

        assert_eq!(folded_expression, expected_expression);
    }
}
