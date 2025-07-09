use crate::hash_matrix::{constmatmul, HashMatrix, A, B};
use alloc::vec::Vec;
use lazy_static::lazy_static;
use seq_macro::seq;

// The hash function is defined in terms of bit operations, corresponding to the
// generator matrices A and B. But of course this would be very slow to do in
// practice; here we generate 256-entry and 65536-entry lookup tables for all one-
// and two-byte hashes
const BIT_LOOKUPS: [HashMatrix; 2] = [B, A];

const fn mul_from_byte(b: u8) -> HashMatrix {
    let bit0 = (b & 1) as usize;
    let bit1 = ((b & (1 << 1)) >> 1) as usize;
    let bit2 = ((b & (1 << 2)) >> 2) as usize;
    let bit3 = ((b & (1 << 3)) >> 3) as usize;
    let bit4 = ((b & (1 << 4)) >> 4) as usize;
    let bit5 = ((b & (1 << 5)) >> 5) as usize;
    let bit6 = ((b & (1 << 6)) >> 6) as usize;
    let bit7 = ((b & (1 << 7)) >> 7) as usize;

    let m0 = BIT_LOOKUPS[bit0];
    let m1 = BIT_LOOKUPS[bit1];
    let m2 = BIT_LOOKUPS[bit2];
    let m3 = BIT_LOOKUPS[bit3];
    let m4 = BIT_LOOKUPS[bit4];
    let m5 = BIT_LOOKUPS[bit5];
    let m6 = BIT_LOOKUPS[bit6];
    let m7 = BIT_LOOKUPS[bit7];

    constmatmul(
        constmatmul(constmatmul(m7, m6), constmatmul(m5, m4)),
        constmatmul(constmatmul(m3, m2), constmatmul(m1, m0)),
    )
}

const fn mul_from_wyde(d: u16) -> HashMatrix {
    constmatmul(
        mul_from_byte(((d & 0xff00) >> 8) as u8),
        mul_from_byte((d & 0xff) as u8),
    )
}

pub(crate) static BYTE_LOOKUPS: [HashMatrix; 256] = seq!(N in 0..256 {
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
