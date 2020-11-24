# Bromberg SL₂ Homomorphic Hashing

This is an implementation of the Tillich-Zémor-style hash function
presented in the paper ["Navigating in the Cayley Graph of SL₂(𝔽ₚ)"
](https://link.springer.com/article/10.1007%2Fs00233-015-9766-5) by
Bromberg, Shpilrain, and Vdovina.

> ## WARNING
> 
> This module is not produced by cryptography experts, but by some
> rando. Furthermore, the algorithm was published in 2017, and is
> itself not at all battle-tested. Only use this library if you either
> (a) know what you're doing and have read and understood our code,
> and/or (b) are building something that does not rely heavily on the
> cryptographic properties of the hash function.
>
> If you _are_ a cryptography expert, we welcome any bug reports or
> pull requests! We also welcome them if you're not a cryptography
> expert; this library is quite simple, and should be easy to grok
> over a coffee with a copy of the paper linked above in hand.


# What is this library for?

This library implements a putatively-strong hash function H with the
following useful property:

For any strings `s1` and `s2`, the hash of their concatenation,
`H(s1 ++ s2)` can be quickly computed from their respective hashes
`H(s1)` and `H(s2)`. In this sense it is a "homomorphic hash function".

This property is especially useful for applications where some very
long string may be constructed via many different routes, but you'd
nonetheless like to be able to quickly rule out unequal strings.

H has some other useful properties, and is in some limited but
potentially-useful sense "provably secure". See Bromberg et al. for
details.

# Technical Details

We use the A(2) and B(2) matrices as generators of SL₂, and
p = 2^127 - 1 for fast modular arithmetic.

There are not yet any benchmarks, and we have not yet attempted to
optimize this library at all. However, we needed an
architecture-agnostic cryptographic hash procedure with a monoid
homomorphism respecting string concatenation, written in a low-level
language. While there are [a](https://github.com/srijs/hwsl2-core)
[few](https://github.com/nspcc-dev/tzhash)
[implementations](https://github.com/phlegmaticprogrammer/tillich_zemor_hash)
of related algorithms, e.g. the venerable [but broken]() Tillich-Zémor hash,
from ["Hashing with SL₂"
](https://link.springer.com/chapter/10.1007/3-540-48658-5_5),
none of them fulfill the above desiderata.
