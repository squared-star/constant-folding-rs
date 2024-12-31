function main() {
    NB. Basic arithmetic
    let basic_add = 15u8;            NB. 5u8 + 10u8
    let basic_sub = 15u8;            NB. 20u8 - 5u8
    let basic_mul = 8u8;             NB. 4u8 * 2u8
    let basic_div = 4u8;             NB. 16u8 / 4u8

    NB. Mixed operators with different precedences
    let mixed_1 = 14u8;         NB. 2u8 + 3u8 * 4u8
    let mixed_2 = 20u8;       NB. (2u8 + 3u8) * 4u8
    let mixed_3 = 8u8;  NB. 10u8 - 2u8 * 3u8 + 4u8
    let mixed_4 = 10u8;   NB. 8u8 / 2u8 + 3u8 * 2u8

    NB. Nested parentheses
    let nested_1 = 5u8; NB. (1u8 + (2u8 * 3u8)) - (4u8 / 2u8)
    let nested_2 = 11u8; NB. ((1u8 + 2u8) * (3u8 - 1u8)) + 5u8
    let nested_3 = 5u8; NB. (((3u8 + 2u8) * 4u8) - 5u8) / (2u8 + 1u8)

    NB. Complex combinations with variables
    let x = 3u8;
    let y = 2u8;
    let z = 5u8;

    let complex_1 = 22u8; NB. (x * y) + (z / 2u8) * 8u8
    let complex_2 = 24u8; NB. ((4u8 + x) * 2u8) - (6u8 / 3u8) + 12u8
    let complex_3 = 9u8; NB. (10u8 - x * y + z) * ((y + y) / 4u8)
    let complex_4 = 69u8;        NB. x * ((y + z) * (4u8 - 1u8)) + 6u8
    let complex_5 = 34u8; NB. (7u8 + x) * (6u8 - y) + (8u8 / y) - (y * z)
}
