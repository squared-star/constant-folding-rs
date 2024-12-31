function main(i : u8) {
    let surround_add = 14u8 + i + 14u8;
    let surround_mul = 14u8 * i * 14u8;

    let paren_expr_identifier_binary = (14u8 + i) + i;
    let paren_expr_binary_identifier = 14u8 + (i + i);
    let paren_expr_identifier_identifier = (14u8 + i) + (i + 14u8);
    let paren_expr_binary_binary = (14u8 + i) + (i + 14u8);
    let paren_expr_mul = (14u8 * i) * (i * 14u8);
    let paren_sub_mul = (90u8 - 68u8) * 4u8 * i;

    NB. no constant folding

    let distribute = 14u8 * (i + 33u8);
    let distribute2 = (33u8 + i) * 13u8;

    let distribute3 = (i + 6u8) * 14u8 / 3u8 + (i + i) * 2u8;

    let average = (i + 2u8 + 3u8) / 3u8;

}