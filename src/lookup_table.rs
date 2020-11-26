use crate::hash_matrix::{A, B, HashMatrix, constmatmul};
use seq_macro::seq;
use lazy_static::lazy_static;

const fn mul8(
    a: HashMatrix,
    b: HashMatrix,
    c: HashMatrix,
    d: HashMatrix,
    e: HashMatrix,
    f: HashMatrix,
    g: HashMatrix,
    h: HashMatrix
) -> HashMatrix {
    constmatmul(
        constmatmul(constmatmul(a, b), constmatmul(c, d)),
        constmatmul(constmatmul(e, f), constmatmul(g, h))
   )
}

const BIT_LOOKUPS: [HashMatrix; 2] = [B, A];

const fn mul_from_byte(b: u8) -> HashMatrix {
    let bit0 = ((b & (1 << 0)) >> 0) as usize;
    let bit1 = ((b & (1 << 1)) >> 1) as usize;
    let bit2 = ((b & (1 << 2)) >> 2) as usize;
    let bit3 = ((b & (1 << 3)) >> 3) as usize;
    let bit4 = ((b & (1 << 4)) >> 4) as usize;
    let bit5 = ((b & (1 << 5)) >> 5) as usize;
    let bit6 = ((b & (1 << 6)) >> 6) as usize;
    let bit7 = ((b & (1 << 7)) >> 7) as usize;

    mul8(BIT_LOOKUPS[bit7], BIT_LOOKUPS[bit6], BIT_LOOKUPS[bit5], BIT_LOOKUPS[bit4],
         BIT_LOOKUPS[bit3], BIT_LOOKUPS[bit2], BIT_LOOKUPS[bit1], BIT_LOOKUPS[bit0])
}

const fn mul_from_wyde(d: u16) -> HashMatrix {
    constmatmul(mul_from_byte((d >> 8) as u8), mul_from_byte(d as u8))
}

pub(crate) static BYTE_LOOKUPS: [HashMatrix; 256] =
seq!(N in 0..256 {
    [
        #( mul_from_byte(N), )*
    ]
});

lazy_static! {
    pub(crate) static ref WYDE_LOOKUPS: Vec<HashMatrix> = {
        let mut l = Vec::with_capacity(65536);
        let mut i: u32 = 0;
        while i < 65536 {
            l.push(mul_from_wyde(i as u16));
            i += 1;
        }
        l
    };
}
