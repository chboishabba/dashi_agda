# F13b guarded positive-denominator fold and H15 complete-Heaps-curve no-go

> **Status update, 28 October 2026 (later cut):** The earlier F13b `ConcreteAddLaw` source-construction gap is now addressed by `DASHI/Statistics/ZipfFractionAddRationalBridgeExact.agda` using standard-library unnormalised-to-reduced rational isomorphism, and consumed by `concreteHurwitzSourceWritten` in `ZipfFractionFoldConditionalExact.agda`. **No Agda kernel typecheck has been executed**, so all earlier statements about missing *kernel-certified* F13b proofs remain true. The authoritative newer proof-status ledger is `Docs/research/zipf_f13b_unreduced_rational_isomorphism_20261028.md`. Keep `finiteZipfWeightIdentificationPaid=false`.
Date: 28 October 2026. Repository PR: https://github.com/chboishabba/dashi_agda/pull/1275.

## O — Objective

Continue original 27-law Zipf max-cut by reusing existing finite fractions, PNF normalization and Heaps chronology. Prove the *structural* fold implication while exposing the one concrete, unpaid rational addition law. Extend the source-level negative result from different Heaps prefixes to **identical complete Heaps curves** with different repeated-token identities. Keep Zipf/Heaps probability model results separate from observed temporal corpora and physical/Monster same-object claims.

## R — Canonical owners and original priority

- `DASHI.Statistics.ZipfFamilyFiniteExact`: existing `Fraction`, `addFraction`, `sumFirst`, `finiteHurwitz`, `finiteHurwitzDenominatorNonZero`.
- `DASHI.Core.FiniteUniformProbabilityNormalizationExact`: original unreduced finite fraction numerator/denominator owner.
- `DASHI.Statistics.ZipfPNFConstructiveNormalizationExact`: F13 source-written finite rational PNF weight normalization, still **kernel pending**.
- `DASHI.Statistics.ZipfHeapsOrderNoGoExact`: preexisting finite rank-to-prefix nonfactorization witness.
- `DASHI.Statistics.ZipfFullHeapsCurveIdentityNoGoExact`: **new** stronger literal sequence countermodel; not a duplicate Heaps expected-value carrier.
- Classical semiring/fraction algebra and 1934 Hardy–Littlewood–Pólya majorization retain mathematical priority. Original research by Heaps, Herdan, Zimmerlin–Louail–Moussallam–Barthelemy (2026) and Santoro–Petri–Tria (2026) remains their own. See https://doi.org/10.1103/543d-frbq and https://doi.org/10.1103/shhp-4dht. Reuse the original identified citation roots; do not claim these papers established this repository's exact finite words.
- New source-level integration/tests: Johl Brown-directed work with OpenAI ChatGPT assistance, 28 October 2026. Earlier Ibrahim Monster 3B ownership is not touched. The separate source-written work of other PRs, including current #1396 evidence governance and #1407 Fourier/codec, is not rebranded as this work.

## C — Fundamental issue found: raw FiniteFraction is not a valid rational

The canonical `FiniteFraction` stores arbitrary `Nat` numerator and denominator. It permits denominator zero, because its original counting application only needs a shared-denominator comparison. A total interpretation `FiniteFraction -> ℚ` preserving source addition and agreeing with `1/1` is **not** a lawful generic rational model across this entire carrier. Example: the raw zero-denominator `0/0` absorbs addition with `1/1`; any homomorphism into rational addition then forces the image of `1/1` to be zero. Thus the earlier unguarded conditional fold specification was too strong and could yield inconsistent premises. It was superseded.

**Fixed:** `DASHI/Statistics/ZipfFractionFoldConditionalExact.agda` explicitly interprets `(a : Fraction)` only given `Nat.NonZero (denominator a)`. Addition preservation requires independent proofs for both inputs and produces the product-denominator proof using the **existing** `NatP.m*n≢0`. The existing `sumFirstDenominatorNonZero` handles the fold; `mandelbrotDenominatorNonZero` handles each Zipf rank term. No global claim about zero-denominator fractions remains.

The resulting theorem has the form:

```
[positive-denominator interpretation]
+ [interpret zeroFraction = 0]
+ [interpret (addFraction a b) = interpret a + interpret b,
   supplied only for separately nonzero denominators]
+ [interpret finiteMandelbrotTerm(r) = rawTerm(r)]
--------------------------------------------------
interpret finiteHurwitz(K,q,s) = rawSum(K,q,s)
```

`finiteFractionFoldHomomorphism` proves the generic finite-fold statement by induction, then `sourceHurwitzEqualsRationalFold` specializes it. The addition/term preservation laws are **explicit fields** of a typed record, not constructed or assumed to be present. The *actual* quotient interpretation of `addFraction` remains to be proved, and `finiteZipfWeightIdentificationPaid=false` remains unchanged. This is a **conditional mathematical theorem**, not unconditional F13b completion.

Relevant standard-library source APIs confirmed by the public Agda documentation:
- https://agda.github.io/agda-stdlib/master/Data.Rational.Base.html
- https://agda.github.io/agda-stdlib/master/Data.Rational.Properties.html
- `normalize-pos`, `pos+nonNeg⇒pos`, `*-inverseʳ`, `nonNeg+nonNeg⇒nonNeg`, `pos*pos⇒pos`.
The Agda compiler is not available in this execution environment. No source is labeled kernel-verified.

## H15 — Same complete curve and histogram do not recover repeated identities

The two separate five-token strings:

```
A B A C B
A B B C A
```

share histogram `(2,2,1)` and *entire* prefix-diversity curve `(0,1,2,2,3,3)`. Their complete novelty flags are `(1,1,0,1,0)`. Yet their third tokens differ: `A` versus `B`. The Agda module defines a three-letter type, `countIf`-based histogram, a general full-prefix curve accumulator, and the no-go theorem `fullCurveCannotRecoverRepeatedIdentity`. It composes equality on the shared curve and universal recovery premises to derive the impossible constructor equality `A≡B`.

This does **not** say the full curve cannot recover *novelty flags*; it can, by adjacent increments. The obstruction is the identity of an already-seen type. It does not identify a Hilberg exponent, model the original 2026 avalanche paper, or give a PDE/Monster theorem.

## F — Exact executable checks and verification ceiling

`tests/test_zipf_f13b_h15_boundary_exact.py` adds seven scoped tests: positive-denominator signed addition, zero-denominator rejection, arbitrary finite fold, source Hurwitz vs normalized masses, full-curve countermodel, exhaustive novelty reconstruction and static source/umbrella/unsafe checks.

A materially equivalent local mathematical replay executed:
- **784** signed two-fraction addition cases, including negative and zero numerators;
- **1,092** finite positive-denominator fold cases;
- **240** shifted Zipf rational/PFN parity cases;
- explicit full-curve and repeated-identity collision plus exhaustive ternary words up to length 6.

All arithmetic assertions passed. The regression file was committed and registered in `scripts/check_zipf_family_acceptance.sh`; the user requested not to prioritize CI. These checks do NOT constitute a compiled Agda certificate or an exact full GitHub-head suite. The two new Agda modules are imported by the canonical `DASHI/Statistics/ZipfFamilyEverything.agda`, itself previously imported by `DASHI/Everything.agda`.

## P0 wall and next Pareto objective

The remaining *specific* formal algebra lemma is:

```
interp (addFraction a b) (productNonZero ha hb)
  ≡ interp a ha + interp b hb
```

where `interp` is the actual standard-library normalized rational quotient `normalize (numerator a) (denominator a)` and `ha,hb` are valid nonzero-denominator witnesses. Only then instantiate `PositiveFractionInterpretation`, prove each term's correspondence with `rawTerm`, and obtain unconditional `sourceHurwitzEqualsRationalFold` on a kernel-checked type.

Do not mark F13b complete from passing Python, a conditional record, syntactic import, matching eigen-motif, source-written lemma, or test fixture. Following this, work on H08 constructive all-prefix extremality, S23 two-sampler stochastic dominance, S24 joint prefix coupling and C17 rare-tail instability. Retain every named primary author and each independent repository/PR proof owner. No protected ESD path was edited.


## Follow-through: specialized quotient interpreter, leaving one premise

The conditional fold proof now also exports an **actual candidate rational interpretation**:

`concreteInterpret a ha = Data.Rational.Base.normalize (numerator a) (denominator a) {{ha}}`.

The source `ConcreteAddLaw` is the single remaining algebraic premise on explicitly positive-denominator inputs. `concreteZeroPreserved` is the definitional rational zero identity; `concreteRankTermPreserved` reuses the existing `rawTermMatchesSource` identity (with symmetry). Under a separately supplied `ConcreteAddLaw`, the already-written `concreteSourceHurwitzEqualsRationalFold` specializes the whole finite Hurwitz sum to the actual rational evaluator. **This is a conditional result; no value inhabiting `ConcreteAddLaw` has been committed or tested by the Agda compiler.**

This specialization narrows the true remaining formal obligation from three hypothetical interpretation laws to **one concrete cross-multiplication/addition compatibility theorem** plus Agda typechecking and any compiler-driven repairs. It does not constitute an unconditional F13b payment, so the original adapter's `finiteZipfWeightIdentificationPaid=false` remains correct.


## H14: general injectivity of a valid novelty-flag curve

The sibling `DASHI/Statistics/ZipfNoveltyCurveInjectiveExact.agda` now formalizes a separate finite fact. Let `curveFromFlags n bs` contain the starting vocabulary count and all prefix counts obtained by incrementing once for `true` and zero for `false`. The source-written `curveFromFlagsInjective` uses list-tail injectivity, `sucNotSelf`, and recursion to derive `bs=cs` from `curveFromFlags n bs=curveFromFlags n cs`. `zeroBasedFlagsInjective` sets n=0. This does **not** claim an unproved invariant for arbitrary invalid numerical curves. It applies to curves actually constructed from valid binary event flags.

`ZipfFullHeapsCurveIdentityNoGoExact` now imports the H14 owner and gives concrete definitional witnesses `leftCurveIsFlagCurve` and `rightCurveIsFlagCurve` for the same binary novelty event vector. Thus H14 and H15 are complementary, not contradictory: the complete exact curve uniquely determines **when first appearances occur**, while it cannot identify **which previously seen type recurs**. Neither a fitted Heaps exponent nor a final vocabulary size carries the information of the full curve.

The independent `tests/test_zipf_h14_novelty_curve_exact.py` adds six focused tests. Materially equivalent local checking passed **10,235** binary flag curves (all lengths 0..10 and five initial vocabulary counts) and **1,227** short original token words (alphabet 1..3 and lengths 0..6). It also checks H15's distinct-repeated-token counterexample. These are exact finite Python checks, NOT Agda kernel receipts. The tests are included in the local acceptance shell, while CI remains deprioritized at the user's instruction.
