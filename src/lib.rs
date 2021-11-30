/*!
This is an implementation of the Tillich-Zémor-style hash function
presented in the paper ["Navigating in the Cayley Graph of SL₂(𝔽ₚ)"
](https://link.springer.com/article/10.1007%2Fs00233-015-9766-5) by
Bromberg, Shpilrain, and Vdovina.

> ### Warning
>
> This module is not produced by cryptography experts, but by
> [some random guy](http://benwr.net). Furthermore, the algorithm
> was published in 2017, and is itself not at all battle-tested. Only
> use this library if you either (a) know what you're doing and have
> read and understood our code, and/or (b) are building something that
> does not rely heavily on the cryptographic properties of the hash
> function.
>
> If you _are_ a cryptography expert, we welcome any bug reports or
> pull requests! We also welcome them if you're not a cryptography
> expert; this library is quite simple, and should be easy to grok
> over a coffee with a copy of the paper linked above in hand.

# What is this library for?

This library implements a putatively-strong hash function H with the
useful property that it gives a monoid homomorphism. This means there
is a cheap operation `*` such that given strings `s1` and `s2`,
`H(s1 ++ s2) = H(s1) * H(s2)`.

This property is especially useful for applications where some very
long string may be constructed via many different routes, but you'd
nonetheless like to be able to quickly rule out unequal strings.

It also allows you to hash _parts_ of your data as you acquire them,
and then merge them later in whatever order is convenient. This allows
for very flexible hashing schemes.

H has some other cool properties, and is in some limited but
potentially-useful sense "provably secure". See Bromberg et al. for
details.

# How to use this library

This library provides the means to construct
[`HashMatrix`](struct.HashMatrix.html)es, using [`hash`](fn.hash.html),
which takes a slice of bytes. These hashes can be compared,
or serialized to hex strings using
[`to_hex`](struct.HashMatrix.html#method.to_hex).

```
use bromberg_sl2::*;
assert_eq!(
  hash("hello, world! It's fun to hash stuff!".as_ref()).to_hex(),
  "01c5cf590d32654c87228c0d66441b200aec1439e54e724f05cd3c6c260634e565594b61988933e826e9705de22884ce007df0f733a371516ddd4ac9237f7a46");
```

Hashes may also be composed, using the `*` operator:

```
use bromberg_sl2::*;
assert_eq!(
  hash("hello, ".as_ref()) * hash("world!".as_ref()),
  hash("hello, world!".as_ref())
);
```

# Technical Details

We use the A(2) and B(2) matrices as generators, and
p = 2^127 - 1 as our prime order, for fast modular arithmetic.

We have not yet attempted to seriously optimize this library, and
performance is a secondary goal. As of right now our procedure is
about 1/3 as fast as SHA3-512.

We needed an architecture-agnostic cryptographic hash procedure with a
monoid homomorphism respecting string concatenation, written in a
low-level language. While there are
[a](https://github.com/srijs/hwsl2-core)
[few](https://github.com/nspcc-dev/tzhash)
[implementations](https://github.com/phlegmaticprogrammer/tillich_zemor_hash)
of related algorithms, e.g. the venerable [but broken
](https://link.springer.com/chapter/10.1007/978-3-642-19574-7_20) Tillich-Zémor hash,
from ["Hashing with SL₂"
](https://link.springer.com/chapter/10.1007/3-540-48658-5_5),
none of them fulfill these desiderata.
*/

#![no_std]

#[macro_use]
extern crate alloc;

// Re-export digest traits
pub use digest::{
    self, generic_array::GenericArray, Digest, DynDigest, FixedOutput, FixedOutputDirty, Reset,
    Update,
};

pub use crate::hash_matrix::{constmatmul, DigestString, HashMatrix};

use crate::lookup_table::{BYTE_LOOKUPS, WYDE_LOOKUPS};

pub use crate::hash_matrix::I;

mod hash_matrix;
mod lookup_table;

/// The main export of this library: Give me a byte
/// stream and I'll give you a hash.
#[must_use]
#[inline]
pub fn hash(bytes: &[u8]) -> HashMatrix {
    let mut acc = I;
    for bs in bytes.chunks(2) {
        if bs.len() == 2 {
            acc = acc * WYDE_LOOKUPS[(((bs[0] as usize) << 8) | (bs[1] as usize))];
        } else {
            acc = acc * BYTE_LOOKUPS[bs[0] as usize];
        }
    }
    acc
}

#[must_use]
#[inline]
#[cfg(feature = "std")]
/// Same as `hash` but computes the hash of the byte stream in parallel.
///
/// The number of threads used is set automatically but can be overridden using the
/// `RAYON_NUM_THREADS` environment variable
pub fn hash_par(bytes: &[u8]) -> HashMatrix {
    use rayon::prelude::*;

    bytes
        .par_chunks(2)
        .fold(
            || I,
            |acc, bs| {
                if bs.len() == 2 {
                    acc * WYDE_LOOKUPS[(((bs[0] as usize) << 8) | (bs[1] as usize))]
                } else {
                    acc * BYTE_LOOKUPS[bs[0] as usize]
                }
            },
        )
        .reduce(
            || I,
            |mut acc, h| {
                acc = acc * h;
                acc
            },
        )
}

/// This procedure implements the same hash function as `hash()`, but
/// with a different performance tradeoff. The first time it's invoked,
/// `hash` computes a 4MiB table of all the hashes for every pair of
/// bytes, which are then used to double hashing speed. For applications
/// that need to do a lot of hashing, this is nearly twice as fast as
/// `hash()`, but it also requires much more memory and initialization
/// time. As a rule of thumb, if you're going to hash less than 100KiB
/// during your program's execution, you should probably use
/// `hash_strict`.
#[must_use]
#[inline]
pub fn hash_strict(bytes: &[u8]) -> HashMatrix {
    let mut acc = I;
    for b in bytes {
        acc = acc * BYTE_LOOKUPS[*b as usize];
    }
    acc
}

/// Things that can be hashed using this crate.
pub trait BrombergHashable {
    fn bromberg_hash(&self) -> HashMatrix;
}

impl BrombergHashable for [u8] {
    #[inline]
    fn bromberg_hash(&self) -> HashMatrix {
        hash(self)
    }
}

impl<T: BrombergHashable> BrombergHashable for &T {
    #[inline]
    fn bromberg_hash(&self) -> HashMatrix {
        (**self).bromberg_hash()
    }
}

impl<T: BrombergHashable> BrombergHashable for &mut T {
    #[inline]
    fn bromberg_hash(&self) -> HashMatrix {
        (**self).bromberg_hash()
    }
}

impl<T: BrombergHashable> BrombergHashable for alloc::boxed::Box<T> {
    #[inline]
    fn bromberg_hash(&self) -> HashMatrix {
        (**self).bromberg_hash()
    }
}

impl<T: BrombergHashable> BrombergHashable for alloc::rc::Rc<T> {
    #[inline]
    fn bromberg_hash(&self) -> HashMatrix {
        (**self).bromberg_hash()
    }
}

impl Update for HashMatrix {
    fn update(&mut self, data: impl AsRef<[u8]>) {
        *self = *self * data.as_ref().bromberg_hash();
    }
}

impl Reset for HashMatrix {
    fn reset(&mut self) {
        *self = I;
    }
}

impl FixedOutputDirty for HashMatrix {
    type OutputSize = digest::consts::U64;

    fn finalize_into_dirty(&mut self, out: &mut GenericArray<u8, Self::OutputSize>) {
        *out = self.generic_array_digest();
    }
}
