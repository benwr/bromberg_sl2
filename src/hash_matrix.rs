use std::fmt::Debug;
use std::ops::Mul;

/// The type of hash values. Takes up 512 bits of space.
/// Can be created only by composition of the provided
/// [`BrombergHashable`](trait.BrombergHashable.html)
/// instances, since not all 512-bit sequences are valid hashes
/// (in fact, fewer than 1/4 of them will be valid).
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct HashMatrix([u128; 4]);

impl HashMatrix {
    /// Produce a hex digest of the hash. This will be 128 hex digits.
    pub fn to_hex(self) -> String {
        format!("{:016x}{:016x}{:016x}{:016x}",
                self.0[0], self.0[1], self.0[2], self.0[3])
    }
}

impl Mul for HashMatrix {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        matmul(self, rhs)
    }
}

pub(crate) static A: HashMatrix = HashMatrix([
    1, 2,
    0, 1,
]);

pub(crate) static B: HashMatrix = HashMatrix([
    1, 0,
    2, 1,
]);

pub(crate) static I: HashMatrix = HashMatrix([
    1, 0,
    0, 1,
]);

const SUCC_P: u128 = 1 << 127;
const P: u128 = SUCC_P - 1;
const NOT_SUCC_P: u128 = !SUCC_P;

// TODO test
fn mod_p(x: u128) -> u128 {
    if x == u128::MAX {
        1
    } else if x > P {
        (x & NOT_SUCC_P) + 1
    } else if x == P {
        0
    } else {
        x
    }
}

const fn const_mod_p(x: u128) -> u128 {
    x % P
}

// TODO test
fn mul_mod_p(x: u128, y: u128) -> u128 {
    // we assume that x and y are less than P, and produce a number
    // less than P.

    // this could probably be made much faster, though I'm not sure.
    // In particular, maybe we should compute the product mod P?
    let xlo = x & 0xffff_ffff_ffff_ffff;
    let ylo = y & 0xffff_ffff_ffff_ffff;

    let xhi = x >> 64;
    let yhi = y >> 64;

    let xhi_ylo = xhi * ylo;
    let yhi_xlo = yhi * xlo;

    let (lo_sum_1, carry_bool_1) = (xhi_ylo << 64).overflowing_add(yhi_xlo << 64);
    let (low_word, carry_bool_2) = lo_sum_1.overflowing_add(xlo * ylo);
    let carry = carry_bool_1 as u128 + carry_bool_2 as u128;

    let high_word = (xhi * yhi) + (xhi_ylo >> 64) + (yhi_xlo >> 64) + carry;

    // 2^128 is 2 mod P, so we can just multiply the high word by 2 and add it.
    // we also know that the high word is < 2^126 since our inputs were <2^127,
    // so the whole product must be <2^254. Taking this all together, we know
    // we can do high_word << 1 to get a number <2^127, leaving just the low
    // word to mod before doing a safe addition in base 128.
    mod_p((high_word << 1) + mod_p(low_word))
}

const fn const_mul_mod_p(x: u128, y: u128) -> u128 {
    let xlo = x & 0xffff_ffff_ffff_ffff;
    let ylo = y & 0xffff_ffff_ffff_ffff;

    let xhi = x >> 64;
    let yhi = y >> 64;

    let xhi_ylo = xhi * ylo;
    let yhi_xlo = yhi * xlo;

    let (lo_sum_1, carry_bool_1) = (xhi_ylo << 64).overflowing_add(yhi_xlo << 64);
    let (low_word, carry_bool_2) = lo_sum_1.overflowing_add(xlo * ylo);
    let carry = carry_bool_1 as u128 + carry_bool_2 as u128;

    let high_word = (xhi * yhi) + (xhi_ylo >> 64) + (yhi_xlo >> 64) + carry;
    const_mod_p((high_word << 1) + const_mod_p(low_word))
}

fn add_mod_p(x: u128, y: u128) -> u128 {
    // NOTE x and y are assumed to be less than P
    mod_p(x + y)
}

const fn const_add_mod_p(x: u128, y: u128) -> u128 {
    const_mod_p(x + y)
}

pub(crate) fn matmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix([
        add_mod_p(mul_mod_p(a.0[0b00], b.0[0b00]),
                  mul_mod_p(a.0[0b01], b.0[0b10])),
        add_mod_p(mul_mod_p(a.0[0b00], b.0[0b01]),
                  mul_mod_p(a.0[0b01], b.0[0b11])),
        add_mod_p(mul_mod_p(a.0[0b10], b.0[0b00]),
                  mul_mod_p(a.0[0b11], b.0[0b10])),
        add_mod_p(mul_mod_p(a.0[0b10], b.0[0b01]),
                  mul_mod_p(a.0[0b11], b.0[0b11])),
    ])
}

/// Has results identical to the `*` operator, but slower.
/// Exposed to provide a `const` version.
pub const fn const_matmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix([
        const_add_mod_p(const_mul_mod_p(a.0[0b00], b.0[0b00]),
                        const_mul_mod_p(a.0[0b01], b.0[0b10])),
        const_add_mod_p(const_mul_mod_p(a.0[0b00], b.0[0b01]),
                        const_mul_mod_p(a.0[0b01], b.0[0b11])),
        const_add_mod_p(const_mul_mod_p(a.0[0b10], b.0[0b00]),
                        const_mul_mod_p(a.0[0b11], b.0[0b10])),
        const_add_mod_p(const_mul_mod_p(a.0[0b10], b.0[0b01]),
                        const_mul_mod_p(a.0[0b11], b.0[0b11])),
    ])
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    #[test]
    fn it_works() {
        assert_eq!(mul_mod_p(P - 1, 2), P - 2);
        assert_eq!(mul_mod_p(P - 1, P - 1), 1);
        assert_eq!(mul_mod_p(4, 4), 16);

        assert_eq!(mod_p(P), 0);
        assert_eq!(mod_p(P + 1), 1);
        assert_eq!(mod_p(0), 0);
        assert_eq!(mod_p(1), 1);
        assert_eq!(mod_p(P - 1), P - 1);
        assert_eq!(mod_p(P + 1), 1);
        assert_eq!(mod_p(u128::MAX), 1);

        assert_eq!(HashMatrix([1, 0, 0, 1])
                   * HashMatrix([1, 0, 0, 1]),
                   HashMatrix([1, 0, 0, 1]));
        assert_eq!(HashMatrix([2, 0, 0, 2])
                   * HashMatrix([2, 0, 0, 2]),
                   HashMatrix([4, 0, 0, 4]));
        assert_eq!(HashMatrix([0, 1, 1, 0])
                   * HashMatrix([2, 0, 0, 2]),
                   HashMatrix([0, 2, 2, 0]));
        assert_eq!(HashMatrix([0, 1, 1, 0])
                   * HashMatrix([2, 0, 0, 2]),
                   HashMatrix([0, 2, 2, 0]));
        assert_eq!(HashMatrix([1, 0, 0, 1])
                   * HashMatrix([P, 0, 0, P]),
                   HashMatrix([0, 0, 0, 0]));
        assert_eq!(HashMatrix([1, 0, 0, 1])
                   * HashMatrix([P + 1, P + 5, 2, P]),
                   HashMatrix([1, 5, 2, 0]));
        assert_eq!(HashMatrix([P + 1, P + 3, P + 4, P + 5])
                   * HashMatrix([P + 1, P, P, P + 1]),
                   HashMatrix([1, 3, 4, 5]));
    }

    use quickcheck::*;
    use num_bigint::*;

    quickcheck! {
        fn composition(a: Vec<u8>, b: Vec<u8>) -> bool {
            let mut a = a;
            let mut b = b;
            let h1 = a.bromberg_hash() * b.bromberg_hash();
            a.append(&mut b);
            a.bromberg_hash() == h1
        }
    }

    quickcheck! {
        fn mul_check(a: u128, b: u128) -> bool {
            let res = mul_mod_p(a, b);

            a.to_biguint().unwrap() * b.to_biguint().unwrap()
                % P.to_biguint().unwrap() == res.to_biguint().unwrap()
        }
    }

    quickcheck! {
        fn add_check(a: u128, b: u128, c: u128, d: u128) -> bool {
            let res = add_mod_p(mul_mod_p(a, b), mul_mod_p(c, d));

            let big_res = (a.to_biguint().unwrap() * b.to_biguint().unwrap()
                           + c.to_biguint().unwrap() * d.to_biguint().unwrap())
                % P.to_biguint().unwrap();

            res.to_biguint().unwrap() == big_res
        }
    }

    quickcheck! {
        fn mod_p_check(a: u128, b: u128, c: u128, d: u128) -> bool {
            let res = mod_p(a);
            let big_res = a % P;

            res == big_res
        }
    }

    quickcheck! {
        fn collision_search(a: Vec<u8>, b: Vec<u8>) -> bool {
            let ares = a.bromberg_hash();
            let bres = b.bromberg_hash();
            ares != bres || a == b
        }
    }
}
