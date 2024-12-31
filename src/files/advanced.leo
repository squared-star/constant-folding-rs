function main(i : u8) -> u8 {
    let a = 5u8 * 5u8;
    let b = 8u8 * a;
    NB. if (true) {
       let a_0 = 5u8 * a;
       return a_0;
    NB. } else {
    NB.    let a_1 = a * a;

    NB. }
    NB. let b = a * 3u8;
    NB. return b;
}