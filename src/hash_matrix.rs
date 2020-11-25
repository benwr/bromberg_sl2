use std::fmt::Debug;
use std::ops::Mul;

#[derive(PartialEq, Eq, Debug)]
// big-end first; does this matter?
struct U256([u128; 2]);

#[cfg(test)]
use num_bigint::*;

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

pub(crate) const I: HashMatrix = HashMatrix([
    1, 0,
    0, 1,
]);

const P: u128 = (1 << 127) - 1;

// lower 64 bits
const fn lo_mask(x: u128) -> u128 {
    x & 0xffff_ffff_ffff_ffff
}

const fn mul(x: u128, y: u128) -> U256 {
    // this could probably be made much faster, though I'm not sure.
    // also I'm not 100% sure it's bug-free; I'm writing it at 1:30am.
    let xhi = x >> 64;
    let yhi = y >> 64;
    let xlo = lo_mask(x);
    let ylo = lo_mask(y); 

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
    // so I thinkwe don't have to worry about carries out of here.
    let (low, carry) = x.0[1].overflowing_add(y.0[1]);
    let high = x.0[0] + y.0[0] + carry as u128;
    U256([high, low])
}

const fn mod_p_round(n: U256) -> U256 {
    let low_bits = n.0[1] & P; // 127 bits of input
    let intermediate_bits = (n.0[0] << 1) | (n.0[1] >> 127); // 128 of the 129 additional bits
    let high_bit = n.0[0] >> 127;
    let (sum, carry_bool) = low_bits.overflowing_add(intermediate_bits);
    U256([carry_bool as u128 + high_bit, sum])
}

const fn mod_p(n: U256) -> u128 {
    // algorithm as described by Dresdenboy in "Fast calculations
    // modulo small mersenne primes like M61" at
    // https://www.mersenneforum.org/showthread.php?t=1955
    let n1 = mod_p_round(n); // n1 is at most 130 bits wide
    let n2 = mod_p_round(n1); // n2 is at most 128 bits wide
    let n3 = mod_p_round(n2); // n3 is at most 127 bits wide

    ((n3.0[1] + 1) & P).saturating_sub(1)
}

/// Identical to the `*` operator; exposed to provide a `const` version.
pub const fn matmul(a: HashMatrix, b: HashMatrix) -> HashMatrix {
    HashMatrix([
        mod_p(add(mul(a.0[0b00], b.0[0b00]), mul(a.0[0b01], b.0[0b10]))),
        mod_p(add(mul(a.0[0b00], b.0[0b01]), mul(a.0[0b01], b.0[0b11]))),
        mod_p(add(mul(a.0[0b10], b.0[0b00]), mul(a.0[0b11], b.0[0b10]))),
        mod_p(add(mul(a.0[0b10], b.0[0b01]), mul(a.0[0b11], b.0[0b11]))),
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
            let h1 = a.bromberg_hash() * b.bromberg_hash();
            a.append(&mut b);
            a.bromberg_hash() == h1
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
            let ares = a.bromberg_hash();
            let bres = b.bromberg_hash();
            ares != bres || a == b
        }
    }
}
