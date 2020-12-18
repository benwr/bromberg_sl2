use alloc::string::String;
use core::fmt::Debug;
use core::ops::Mul;

#[cfg(test)]
use alloc::vec::Vec;

#[derive(PartialEq, Eq, Debug)]
// big-end first; does this matter?
// TODO try using u64s or u32s instead for performance.
struct U256([u128; 2]);

#[cfg(test)]
use num_bigint::{BigUint, ToBigUint};

#[cfg(test)]
impl ToBigUint for U256 {
    fn to_biguint(&self) -> Option<BigUint> {
        Some(self.0[0].to_biguint().unwrap()
             * (1.to_biguint().unwrap() << 128)
             + self.0[1].to_biguint().unwrap())
    }
}


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

pub(crate) const A: HashMatrix = HashMatrix([
    1, 2,
    0, 1,
]);

pub(crate) const B: HashMatrix = HashMatrix([
    1, 0,
    2, 1,
]);

pub static I: HashMatrix = HashMatrix([
    1, 0,
    0, 1,
]);

const SUCC_P: u128 = 1 << 127;
const P: u128 = SUCC_P - 1;

const fn mul(x: u128, y: u128) -> U256 {
    // this could probably be made much faster, though I'm not sure.
    let xlo = x & 0xffff_ffff_ffff_ffff;
    let ylo = y & 0xffff_ffff_ffff_ffff;

    let xhi = x >> 64;
    let yhi = y >> 64;

    let xhi_ylo = xhi * ylo;
    let yhi_xlo = yhi * xlo;

    let (lo_sum_1, carry_bool_1) = (xhi_ylo << 64).overflowing_add(yhi_xlo << 64);
    let (lo_sum_2, carry_bool_2) = lo_sum_1.overflowing_add(xlo * ylo);
    let carry = carry_bool_1 as u128 + carry_bool_2 as u128;

    U256([(xhi * yhi) + (xhi_ylo >> 64) + (yhi_xlo >> 64) + carry, lo_sum_2])
}

const fn add(x: U256, y: U256) -> U256 {
    // NOTE: x and y are guaranteed to be <=
    // (2^127 - 2)^2 = 2^254 - 4 * 2^127 + 4,
    // so I think we don't have to worry about carries out of here.
    let (low, carry) = x.0[1].overflowing_add(y.0[1]);
    let high = x.0[0] + y.0[0] + carry as u128;
    U256([high, low])
}

// algorithm as described by Dresdenboy in "Fast calculations
// modulo small mersenne primes like M61" at
// https://www.mersenneforum.org/showthread.php?t=1955
// I tried using a handwritten version of this that avoided the U256s,
// but it was like half as fast somehow.
const fn mod_p_round_1(n: U256) -> U256 {
    let low_bits = n.0[1] & P; // 127 bits of input
    let intermediate_bits = (n.0[0] << 1) | (n.0[1] >> 127); // 128 of the 129 additional bits
    let high_bit = n.0[0] >> 127;
    let (sum, carry_bool) = low_bits.overflowing_add(intermediate_bits);
    U256([carry_bool as u128 + high_bit, sum])
}

const fn mod_p_round_2(n: U256) -> U256 {
    let low_bits = n.0[1] & P; // 127 bits of input
    let intermediate_bits = (n.0[0] << 1) | (n.0[1] >> 127); // 128 of the 129 additional bits
    U256([0, low_bits + intermediate_bits])
}

const fn mod_p_round_3(n: U256) -> U256 {
    let low_bits = n.0[1] & P; // 127 bits of input
    let intermediate_bit = n.0[1] >> 127; // 128 of the 129 additional bits
    U256([0, low_bits + intermediate_bit])
}

const fn constmod_p(n: U256) -> u128 {
    let n1 = mod_p_round_1(n); // n1 is at most 130 bits wide
    let n2 = mod_p_round_2(n1); // n2 is at most 128 bits wide
    let n3 = mod_p_round_3(n2); // n3 is at most 127 bits wide

    ((n3.0[1] + 1) & P).saturating_sub(1)
}

fn mod_p(mut n: U256) -> u128 {
    // n is at most 255 bits wide
    if n.0[0] != 0 {
        n = mod_p_round_1(n);
    }
    // n is at most 129 bits wide
    if n.0[0] != 0 || (n.0[1] > P) {
        n = mod_p_round_2(n);
    }
    // n is at most 128 bits wide
    if n.0[1] > P {
        n = mod_p_round_3(n);
    }
    // n is at most 127 bits wide

    if n.0[1] == P {
        0
    } else {
        n.0[1]
    }
}

pub fn matmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix([
        mod_p(add(mul(a.0[0b00], b.0[0b00]), mul(a.0[0b01], b.0[0b10]))),
        mod_p(add(mul(a.0[0b00], b.0[0b01]), mul(a.0[0b01], b.0[0b11]))),
        mod_p(add(mul(a.0[0b10], b.0[0b00]), mul(a.0[0b11], b.0[0b10]))),
        mod_p(add(mul(a.0[0b10], b.0[0b01]), mul(a.0[0b11], b.0[0b11]))),
    ])
}

/// Identical results to the `*` operator, but slower. Exposed to provide a
/// `const` version in case you'd like to compile certain hashes into your
/// binaries.
pub const fn constmatmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix([
        constmod_p(add(mul(a.0[0b00], b.0[0b00]), mul(a.0[0b01], b.0[0b10]))),
        constmod_p(add(mul(a.0[0b00], b.0[0b01]), mul(a.0[0b01], b.0[0b11]))),
        constmod_p(add(mul(a.0[0b10], b.0[0b00]), mul(a.0[0b11], b.0[0b10]))),
        constmod_p(add(mul(a.0[0b10], b.0[0b01]), mul(a.0[0b11], b.0[0b11]))),
    ])
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    #[test]
    fn it_works() {
        assert_eq!(mul(1 << 127, 2), U256([1,0]));
        assert_eq!(mul(1 << 127, 1 << 127),
            U256([85070591730234615865843651857942052864, 0]));
        assert_eq!(mul(4, 4), U256([0, 16]));
        assert_eq!(mul((1 << 127) + 4, (1 << 127) + 4),
            U256([85070591730234615865843651857942052868, 16]));

        assert_eq!(mod_p(U256([0, P])), 0);
        assert_eq!(mod_p(U256([0, P + 1])), 1);
        assert_eq!(mod_p(U256([0, 0])), 0);
        assert_eq!(mod_p(U256([0, 1])), 1);
        assert_eq!(mod_p(U256([0, P - 1])), P - 1);
        assert_eq!(mod_p(U256([0, 1 << 127])), 1);
        assert_eq!(mod_p(U256([1, P])), 2);
        assert_eq!(mod_p(U256([1, 0])), 2);
        assert_eq!(mod_p(U256([P, 0])), 0);
        assert_eq!(mod_p(U256([P, P])), 0);
        assert_eq!(mod_p(U256([0, u128::MAX])), 1);

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

    quickcheck! {
        fn composition(a: Vec<u8>, b: Vec<u8>) -> bool {
            let mut a = a;
            let mut b = b;
            let h1 = hash(&a) * hash(&b);
            a.append(&mut b);
            hash(&a) == h1
        }
    }

    quickcheck! {
        fn mul_check(a: u128, b: u128) -> bool {
            use num_bigint::*;
            let res = mul(a, b);

            a.to_biguint().unwrap() * b.to_biguint().unwrap()
                == res.to_biguint().unwrap()
        }
    }

    quickcheck! {
        fn add_check(a: u128, b: u128, c: u128, d: u128) -> bool {
            let res = add(mul(a, b), mul(c, d));

            let big_res = a.to_biguint().unwrap() * b.to_biguint().unwrap()
                + c.to_biguint().unwrap() * d.to_biguint().unwrap();

            res.to_biguint().unwrap() == big_res
        }
    }

    quickcheck! {
        fn mod_p_check(a: u128, b: u128, c: u128, d: u128) -> bool {
            let res = mod_p(add(mul(a, b), mul(c, d)));

            let big_res = (a.to_biguint().unwrap() * b.to_biguint().unwrap()
                + c.to_biguint().unwrap() * d.to_biguint().unwrap())
                % P.to_biguint().unwrap();

            res.to_biguint().unwrap() == big_res
        }
    }

    quickcheck! {
        fn collision_search(a: Vec<u8>, b: Vec<u8>) -> bool {
            let ares = hash(&a);
            let bres = hash(&b);
            ares != bres || a == b
        }
    }
}
