# E8 norm-two exhaustion: mathematical proof and source-weld contract

**Scope:** non-computational, all-vector classification of the standard coordinate model of the positive-definite E8 lattice. This is a mathematical proof, **not** an Agda 2.9 kernel receipt, and does not identify an independently selected repository carrier without an explicit map.

## Definition and normalization

Let
[
L = {xinmathbb Z^8:sum_{i=1}^8x_iin 2mathbb Z}
cup
{xin(mathbb Z+	frac12)^8:sum_{i=1}^8x_iin 2mathbb Z}.
]
The norm is the Euclidean (xcdot x=sum_i x_i^2).
Set (d_i=2x_i). The two cases correspond to all (d_i) even or all (d_i) odd, together with (sum_i d_iequiv0pmod4).
The norm-two condition is precisely (sum_i d_i^2=8).

## Theorem (all native norm-two vectors)

Every (xin L) with (xcdot x=2) has exactly one of the following shapes:

1. **Integer family:** exactly two coordinates equal (pm1), the other six zero. Each choice is allowed by the even coordinate-sum condition. There are (inom82cdot 2^2=112) vectors.
2. **Half-integer family:** every coordinate is (pm	frac12), and the number of negative coordinates is even. There are (sum_{k mathrm{even}}inom8k=2^7=128) vectors.

Consequently the complete norm-two shell has exactly (112+128=240) vectors.

### Proof

If (x) is integral, each (x_i^2) is a nonnegative integer. Since the sum is 2, the only possibilities for the multiset of nonzero squares are ({2}) or ({1,1}). A square of an integer cannot be 2, so only ({1,1}) occurs. Thus exactly two coordinates have absolute value 1; their sum is one of (-2,0,2), hence even, and all four signs at each selected pair are allowed.

If (x) is half-integral, (|x_i|ge1/2), so (sum_i x_i^2ge8/4=2). Equality forces each (|x_i|=1/2), since every summand is at least (1/4). If (k) of the eight signs are negative, (sum_i x_i=(8-2k)/2=4-k). This is even iff (k) is even. Flipping one prescribed sign pairs even-(k) and odd-(k) choices, so there are exactly half of all (2^8) sign choices, namely 128. The integral and half-integral families are disjoint. This proves both completeness and the count. QED.

This proof does **not** infer a correspondence between 240 E8 roots and the distinct 243-element triadic carrier. It does not use any numerical theta coefficients beyond the norm-two shell.

## Exact Agda source-weld obligations

The following are **proposed declaration names/contracts**, not assertions that they exist:

- `originalNativeE8MembershipIffDoubledParityAndSumModFour`: the selected original carrier is equivalent to the all-even/all-odd doubled-coordinate model with total residue 0 mod 4.
- `originalIntegerNormEightImpliesTwoUnitCoordinates`: for all-even doubled vectors, norm 8 implies exactly two entries equal ±2 and six entries zero.
- `originalHalfNormEightImpliesAllUnitCoordinates`: for all-odd doubled vectors, norm 8 implies each entry ±1.
- `originalHalfLatticeSumEvenIffEvenNegativeSigns`: parity of negative signs is exactly the half-integer E8 integrality requirement.
- `originalE8GeneratedRootsExhaustNativeNormTwoLattice`: two-way membership and injective/no-duplicate match to the existing 112+128 generated indexed root list.
- `originalE8NativeNormTwoRootsComplete`: derive 240 from the source-selected shell, not from an assumed count or a finite sample.

## Relation to the already-written all-index results

`AbelE8HalfOddShellInvolutionExact` gives an all-index norm-preserving sign-flip on the half family and an explicit two-sided transport of parity-selected coordinate shells. `AbelE8ThetaParityProjectorExact` gives the algebraic signed theta projector for arbitrary shell indices. Neither requires the present norm-two classification, and neither establishes `Theta_E8=E4` without the finite-shell cardinality transport and the analytic Jacobi theta identity or modular uniqueness.

## Unpaid analytic leaves

1. Same-source equivalence between these doubled coordinates and the original Agda E8 lattice, plus the proof that the root generator enumerates the two cases above with no omissions or collisions.
2. For every (n), finite enumerability and cancellation of half-family E8 shell counts via the existing involution; exact coefficient identification with Jacobi theta power series.
3. Bishop-complex convergence and reindexing of theta series, and either the source-native Jacobi-to-Eisenstein identity or weight-four modularity plus (dim M_4(SL_2(mathbb Z))=1).
4. Original unit-disk equality with Bishop E4, then discriminant nonvanishing / same-source j.
5. Pinned Agda 2.9 `--safe` exact-head acceptance. No gate is promoted to *kernel complete* by this note.
