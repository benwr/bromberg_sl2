use alloc::string::String;
use digest::{consts::U64, generic_array};
use core::fmt::Debug;
use core::ops::Mul;

#[cfg(test)]
use alloc::vec::Vec;

#[derive(PartialEq, Eq, Debug)]
// big-end first; does this matter?
// TODO try using u64s or u32s instead for performance.
struct U256(u128, u128);

#[cfg(test)]
use num_bigint::{BigUint, ToBigUint};

#[cfg(test)]
impl ToBigUint for U256 {
    fn to_biguint(&self) -> Option<BigUint> {
        Some(self.0.to_biguint().unwrap()
             * (1.to_biguint().unwrap() << 128)
             + self.1.to_biguint().unwrap())
    }
}


/// The type of hash values. Takes up 512 bits of space.
/// Can be created only by composition of the provided
/// [`BrombergHashable`](trait.BrombergHashable.html)
/// instances, since not all 512-bit sequences are valid hashes
/// (in fact, fewer than 1/4 of them will be valid).
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct HashMatrix(u128, u128, u128, u128);

impl HashMatrix {
    /// Produce a hex digest of the hash. This will be 128 hex digits.
    #[must_use]
    #[inline]
    pub fn to_hex(self) -> String {
        format!("{:016x}{:016x}{:016x}{:016x}",
                self.0, self.1, self.2, self.3)
    }

    #[must_use]
    #[inline]
    pub(crate) fn generic_array_digest(&self) -> generic_array::GenericArray<u8, U64> {
        use core::iter::once;

        digest::generic_array::GenericArray::from_exact_iter(
            once(self.0)
                .chain(once(self.1))
                .chain(once(self.2))
                .chain(once(self.3))
                .flat_map(|x| x.to_le_bytes()),
        )
        .unwrap()
    }
}

impl Mul for HashMatrix {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        matmul(self, rhs)
    }
}

pub(crate) const A: HashMatrix = HashMatrix(
    1, 2,
    0, 1,
);

pub(crate) const B: HashMatrix = HashMatrix(
    1, 0,
    2, 1,
);

pub static I: HashMatrix = HashMatrix(
    1, 0,
    0, 1,
);

const SUCC_P: u128 = 1 << 127;
const P: u128 = SUCC_P - 1;

#[inline]
const fn mul(x: u128, y: u128) -> U256 {
    // this could probably be made much faster, though I'm not sure.
    let x_lo = x & 0xffff_ffff_ffff_ffff;
    let y_lo = y & 0xffff_ffff_ffff_ffff;

    let x_hi = x >> 64;
    let y_hi = y >> 64;

    let x_hi_y_lo = x_hi * y_lo;
    let y_hi_x_lo = y_hi * x_lo;

    let (lo_sum_1, carry_bool_1) = (x_hi_y_lo << 64).overflowing_add(y_hi_x_lo << 64);
    let (lo_sum_2, carry_bool_2) = lo_sum_1.overflowing_add(x_lo * y_lo);
    let carry = carry_bool_1 as u128 + carry_bool_2 as u128;

    U256((x_hi * y_hi) + (x_hi_y_lo >> 64) + (y_hi_x_lo >> 64) + carry, lo_sum_2)
}

#[inline]
const fn add(x: U256, y: U256) -> U256 {
    // NOTE: x and y are guaranteed to be <=
    // (2^127 - 2)^2 = 2^254 - 4 * 2^127 + 4,
    // so I think we don't have to worry about carries out of here.
    let (low, carry) = x.1.overflowing_add(y.1);
    let high = x.0 + y.0 + carry as u128;
    U256(high, low)
}

// algorithm as described by Dresdenboy in "Fast calculations
// modulo small mersenne primes like M61" at
// https://www.mersenneforum.org/showthread.php?t=1955
// I tried using a handwritten version of this that avoided the U256s,
// but it was like half as fast somehow.
#[inline]
const fn mod_p_round_1(n: U256) -> U256 {
    let low_bits = n.1 & P; // 127 bits of input
    let intermediate_bits = (n.0 << 1) | (n.1 >> 127); // 128 of the 129 additional bits
    let high_bit = n.0 >> 127;
    let (sum, carry_bool) = low_bits.overflowing_add(intermediate_bits);
    U256(carry_bool as u128 + high_bit, sum)
}

#[inline]
const fn mod_p_round_2(n: U256) -> u128 {
    let low_bits = n.1 & P; // 127 bits of input
    let intermediate_bits = (n.0 << 1) | (n.1 >> 127); // 128 of the 129 additional bits
    low_bits + intermediate_bits
}

#[inline]
const fn mod_p_round_3(n: u128) -> u128 {
    let low_bits = n & P; // 127 bits of input
    let intermediate_bit = n >> 127; // 128 of the 129 additional bits
    low_bits + intermediate_bit
}

#[inline]
const fn constmod_p(n: U256) -> u128 {
    let n1 = mod_p_round_1(n);
    let n2 = mod_p_round_2(n1);
    let n3 = mod_p_round_3(n2);

    ((n3 + 1) & P).saturating_sub(1)
}

#[inline]
fn mod_p(mut n: U256) -> u128 {
    // n is at most 255 bits wide
    if n.0 != 0 {
        n = mod_p_round_1(n);
    }
    // n is at most 129 bits wide
    let mut n_small = if n.0 != 0 || (n.1 > P) {
        mod_p_round_2(n)
    } else {
        n.1
    };
    // n is at most 128 bits wide
    if n_small > P {
        n_small = mod_p_round_3(n_small);
    }
    // n is at most 127 bits wide

    if n_small == P {
        0
    } else {
        n_small
    }
}

#[inline]
pub fn matmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix(
        mod_p(add(mul(a.0, b.0), mul(a.1, b.2))),
        mod_p(add(mul(a.0, b.1), mul(a.1, b.3))),
        mod_p(add(mul(a.2, b.0), mul(a.3, b.2))),
        mod_p(add(mul(a.2, b.1), mul(a.3, b.3))),
    )
}

/// Identical results to the `*` operator, but slower. Exposed to provide a
/// `const` version in case you'd like to compile certain hashes into your
/// binaries.
#[must_use]
#[inline]
pub const fn constmatmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix(
        constmod_p(add(mul(a.0, b.0), mul(a.1, b.2))),
        constmod_p(add(mul(a.0, b.1), mul(a.1, b.3))),
        constmod_p(add(mul(a.2, b.0), mul(a.3, b.2))),
        constmod_p(add(mul(a.2, b.1), mul(a.3, b.3))),
    )
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;
    #[test]
    fn it_works() {
        assert_eq!(mul(1 << 127, 2), U256(1,0));
        assert_eq!(mul(1 << 127, 1 << 127),
            U256(85070591730234615865843651857942052864, 0));
        assert_eq!(mul(4, 4), U256(0, 16));
        assert_eq!(mul((1 << 127) + 4, (1 << 127) + 4),
            U256(85070591730234615865843651857942052868, 16));

        assert_eq!(mod_p(U256(0, P)), 0);
        assert_eq!(mod_p(U256(0, P + 1)), 1);
        assert_eq!(mod_p(U256(0, 0)), 0);
        assert_eq!(mod_p(U256(0, 1)), 1);
        assert_eq!(mod_p(U256(0, P - 1)), P - 1);
        assert_eq!(mod_p(U256(0, 1 << 127)), 1);
        assert_eq!(mod_p(U256(1, P)), 2);
        assert_eq!(mod_p(U256(1, 0)), 2);
        assert_eq!(mod_p(U256(P, 0)), 0);
        assert_eq!(mod_p(U256(P, P)), 0);
        assert_eq!(mod_p(U256(0, u128::MAX)), 1);

        assert_eq!(HashMatrix(1, 0, 0, 1)
                   * HashMatrix(1, 0, 0, 1),
                   HashMatrix(1, 0, 0, 1));
        assert_eq!(HashMatrix(2, 0, 0, 2)
                   * HashMatrix(2, 0, 0, 2),
                   HashMatrix(4, 0, 0, 4));
        assert_eq!(HashMatrix(0, 1, 1, 0)
                   * HashMatrix(2, 0, 0, 2),
                   HashMatrix(0, 2, 2, 0));
        assert_eq!(HashMatrix(0, 1, 1, 0)
                   * HashMatrix(2, 0, 0, 2),
                   HashMatrix(0, 2, 2, 0));
        assert_eq!(HashMatrix(1, 0, 0, 1)
                   * HashMatrix(P, 0, 0, P),
                   HashMatrix(0, 0, 0, 0));
        assert_eq!(HashMatrix(1, 0, 0, 1)
                   * HashMatrix(P + 1, P + 5, 2, P),
                   HashMatrix(1, 5, 2, 0));
        assert_eq!(HashMatrix(P + 1, P + 3, P + 4, P + 5)
                   * HashMatrix(P + 1, P, P, P + 1),
                   HashMatrix(1, 3, 4, 5));
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

    #[cfg(feature = "std")]
    quickcheck! {
        fn par_equiv(a: Vec<u8>) -> bool {
            let h0 = hash(&a);
            let h1 = hash_par(&a);
            h0 == h1
        }
    }
}
