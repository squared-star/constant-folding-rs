function main(i : u8) {
    let surround_add = 28u8 + i;
    let surround_mul = 196u8 * i;
    let paren_expr_identifier_binary = 14u8 + i + i;
    let paren_expr_binary_identifier = 14u8 + i + i;
    let paren_expr_identifier_identifier = 28u8 + i + i;
    let paren_expr_binary_binary = 28u8 + i + i;
    let paren_expr_mul = 196u8 * i * i;
    let paren_sub_mul = 88u8 * i;
    let distribute = 14u8 * (33u8 + i);
    let distribute2 = 13u8 * (33u8 + i);
    let distribute3 = 14u8 * (6u8 + i) / 3u8 + 2u8 * (i + i);
    let average = (5u8 + i) / 3u8;
}