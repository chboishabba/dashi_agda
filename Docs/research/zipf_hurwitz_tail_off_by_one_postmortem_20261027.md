# Corrected Hurwitz tail comparison and P0 graph integration

Date: 2026-10-27. Scope: the **same** 27-topic Zipf-family PR #1275.

## Found concrete false inequality (not a hypothetical risk)

Original `scripts/zipf_family_formal.py:hurwitz_tail_bound` returned
`((q+n)^(1-s)/(s-1), (q+n)^(1-s)/(s-1)+(q+n)^(-s))` as lower/upper
bounds on `T_n(s,q)=Σ_(r=n+1)^∞(r+q)^(-s)`.
That old **lower bound was invalid**: for `s=2, q=1, n=5`, the actual
tail `Σ_(r=6)^∞(r+1)^(-2)=ζ(2,7)≈0.15354517795933756`
is **less** than the previously asserted `1/6≈0.16666666666666666`.

The previous regression calculated `Σ_(x=6)^∞x^(-2)`, which starts at
**denominator 6**, whereas the declared shifted tail starts at
**denominator 7**. A second independent mismatch disguised the first;
the old 103-test local result was therefore NOT a valid tail-bound receipt.

## Repaired, original-mathematics attribution

For `s>1`, `q>=0`, `n>=1` and `f(x)=(x+q)^(-s)`, `f` is
positive and decreasing. The classical integral comparison gives

`∫_(n+1)^∞ f(x)dx <= Σ_(r=n+1)^∞ f(r) <= ∫_n^∞ f(x)dx`.

Evaluating the integrals gives exactly

`(n+q+1)^(1-s)/(s-1) <= T_n(s,q) <= (n+q)^(1-s)/(s-1)`.

For `s=2,q=1,n=5`, the corrected values are **1/7** and **1/6**.
This comparison and the Hurwitz recurrence are classical mathematics, not
a new theorem authored by our repository. Authoritative source:
**NIST DLMF §25.11**, https://dlmf.nist.gov/25.11 .

Fix SHA `57333cd5`; independent shifted-tail test fix SHA `93d44f76`.
The regression enumerates the actual `(r+q)^(-s)` terms for multiple
shifts/exponents and accounts for the remaining omitted positive tail.
The exact old test's shifted lower-bound failure was independently
confirmed with `scipy.special.zeta` in a local analysis, but that
numerical library is NOT required by the committed Python test suite.

## Import ownership / current P0

`DASHI/Statistics/ZipfFamilyEverything.agda` imports the three
source-written Agda owners. It is now explicitly imported by the
existing canonical root `DASHI/Everything.agda`, avoiding a disconnected
formalization island. This is source integration, NOT typechecking.

CI workflow `.github/workflows/zipf_family_p0.yml` has separate
exact-checkout Python and Agda jobs. It was submitted on the same PR.
No corresponding successful run was confirmed in this session. Agda
is absent from the local environment. Do NOT report a kernel-verified theorem.

The 27-topic machine registry, observation-level source distinctions,
Original-linguistic law claim boundaries, original Ibrahim Monster 3B
ownership and nonpromotion of matching fingerprints all remain in place.

## Next precise work

Verify CI's exact GitHub checkout, fix any Agda compiler errors *from the
actual compiler output*, prove constructive finite probability
normalization in the already-owned PNF carrier, then assess source-backed
real language/social/bibliometric samples without turning conjectured
Zipf/Benford/Heaps/Price empirical laws into universal assertions.
