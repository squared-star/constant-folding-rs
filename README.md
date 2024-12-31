# Constant Folding in Rust

This repository contains an implementation of a constant folding optimization for a Rust-based language parser and interpreter.
Constant folding is a compiler optimization technique that evaluates constant expressions at compile time rather than at runtime,
improving efficiency by reducing the amount of work needed during execution.

## Features

- **Constant Folding**  
  Simplifies expressions involving constants at compile time. For example, `2 + 3 * 4` is replaced with `14` before runtime.  
  Currently, basic arithmetic operations (addition, subtraction, multiplication, and division) are supported.

- **Support for `u8` Type**  
  The system specifically supports constant folding for `u8` integers, with checks for overflow or division by zero to ensure safety.

- **Handling of Parentheses**  
  Parentheses are respected, ensuring expressions are evaluated in the correct order.

- **Symbol Table Integration**  
  A symbol table is used to keep track of known (compile-time) variable values, allowing them to be replaced in expressions.

## Key Functions Overview

### `constant_folding`

A convenience wrapper function that applies constant folding on a given `Value`. It sets up the necessary context
(such as the symbol table) before calling the core folding logic.

### `value_constant_folding`

Processes a `Value` to fold constants:

- If the value is an integer, it is returned as-is.
- If it is an identifier, the symbol table is checked for a known constant value to replace it.
- If it is an expression, the function recursively folds any constants within.

### `binary_constant_folding`

Optimizes binary expressions by evaluating and simplifying arithmetic operations. It recursively folds the left and right
subexpressions, respecting operator precedence and applying commutative and associative transformations where appropriate.

## Error Handling

A custom `ConstantFoldingError` enum handles errors that may occur during the constant folding process:

- **Overflow**: Triggered when an arithmetic operation exceeds `u8` limits.
- **DivisionByZero**: Triggered when a division by zero is attempted.

## Usage

This project can be integrated into a Rust-based language parser or interpreter to optimize expressions before runtime.
Simply integrate the functions provided into your compilation phase to reduce runtime computation.

## Testing Overview

A variety of tests ensure correctness and robustness:

### 1. Parsing and Constant Folding Tests

- **`test_constant_folding_and_parsing`**: Verifies end-to-end parsing of a `.leo` file, applies constant folding, and compares the result to an expected output.
- **`test_constant_folding_with_inputs_and_parsing`**: Similar to the above but includes test files that contain input parameters.

### 2. Basic Constant Folding Tests

- **`test_constant_folding`**: Checks that an identifier (`x`) is replaced by its known value (`5`) from the symbol table.
- **`test_constant_folding_expression`**: Tests simple arithmetic folding involving an identifier.
- **`test_constant_folding_expression_multiply`**: Verifies multiplication (`5 * 5`) is correctly folded.

### 3. Complex Expression Folding Tests

- **`test_constant_folding_expression_add`**: Validates folding in an expression involving addition and multiplication.
- **`test_constant_folding_multiply_with_addition`**: Ensures correct folding of multiplication when combined with addition.
- **`test_constant_folding_multiply_with_subtraction`**: Similar checks for subtraction combined with multiplication.
- **`test_constant_folding_add_with_multiplication`**: Verifies folding of addition with multiplication across multiple variables.

### 4. Error Handling Tests

- **`test_constant_folding_division_by_zero`**: Confirms division by zero triggers a `DivisionByZero` error.
- **`test_constant_folding_addition_overflow`**: Ensures adding values that exceed `u8` triggers an `Overflow` error.
- **`test_constant_folding_multiplication_overflow`**: Similar test for multiplication overflow.

### 5. Partial and No Folding Impact Tests

- **`test_partial_constant_folding_addition_with_undefined_variable`**: Demonstrates partial folding when one variable is undefined.
- **`test_no_folding_impact_with_undefined_variables`**: Ensures expressions remain semantically unchanged if folding cannot be applied.

### 6. Complex Scenarios

- **`test_constant_folding_multiplication_precedence`**: Validates respect for operator precedence.
- **`test_constant_folding_addition_with_multiplication_on_the_right_nested`**: Tests nested expressions mixing addition and multiplication.

### Running Tests

Run all tests with:

```sh
cargo test
```

This command executes all test cases and reports any failures or issues encountered during the constant folding process.

## Parsing Improvements

The original parser had issues handling deeply nested parenthesized expressions. These have been addressed to ensure
consistent parsing in complex scenarios.

## Future Enhancements

- **Support for More Data Types**: Extend constant folding to `u16`, `u32`, and potentially other integer types.
- **More Complex Expressions**: Enhance the system to handle more intricate expressions and operator combinations.
- **Further Optimizations**: Integrate additional compiler optimizations, such as dead code elimination or loop unrolling.
- **Simplified Codebase**: Refactor and break down the `binary_constant_folding` function into smaller pieces for improved clarity.
- **Parsing Improvements**: Address parsing limitations related to input parameters. Current workarounds are in place, but further refinement is planned to seamlessly integrate with the rest of the system.
