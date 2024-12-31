function main() {
    NB. Basic arithmetic
    let basic_add = 5u8 + 10u8;            NB. Adding two numbers
    let basic_sub = 20u8 - 5u8;            NB. Subtracting two numbers
    let basic_mul = 4u8 * 2u8;             NB. Multiplying two numbers
    let basic_div = 16u8 / 4u8;            NB. Dividing two numbers

    NB. Mixed operators with different precedences
    let mixed_1 = 2u8 + 3u8 * 4u8;         NB. Testing precedence of multiplication over addition
    let mixed_2 = (2u8 + 3u8) * 4u8;       NB. Forcing addition before multiplication with parentheses
    let mixed_3 = 10u8 - 2u8 * 3u8 + 4u8;  NB. Mixed subtraction, multiplication, and addition
    let mixed_4 = 8u8 / 2u8 + 3u8 * 2u8;   NB. Mixed division, addition, and multiplication

    NB. Nested parentheses
    let nested_1 = (1u8 + (2u8 * 3u8)) - (4u8 / 2u8); NB. Nested parentheses with mixed operations
    let nested_2 = ((1u8 + 2u8) * (3u8 - 1u8)) + 5u8; NB. Multiple levels of nesting with different operations
    let nested_3 = (((3u8 + 2u8) * 4u8) - 5u8) / (2u8 + 1u8); NB. Complex nested parentheses with all operations

    NB. Complex combinations with variables
    let x = 3u8;
    let y = 2u8;
    let z = 5u8;

    let complex_1 = (x * y) + (z / 2u8) * 8u8; NB. Complex expression with variables
    let complex_2 = ((4u8 + x) * 2u8) - (6u8 / 3u8) + 12u8; NB. Complex expression with variables
    let complex_3 = (10u8 - x * y + z) * ((y + y) / 4u8); NB. Complex expression with variables
    let complex_4 = x * ((y + z) * (4u8 - 1u8)) + 6u8; NB. Complex expression with variables
    let complex_5 = (7u8 + x) * (6u8 - y) + (8u8 / y) - (y * z); NB. Complex expression with variables
}
