# Zipf F13: constructive rational normalization into canonical PNF (2026-10-28)

## Exact scope, authority and attribution

This is the original **27-topic** Zipf-family PR #1275, not an additional law. Original finite rank/power-law work belongs to Estoup, Zipf, Mandelbrot and Hurwitz. Standard rational normalization, finite additive induction, positivity and reciprocal identities belong to classical algebra and the Agda standard-library contributors. Prior repository proof owners of `DASHI.Core.FiniteUniformProbabilityNormalizationExact`, `DASHI.Cognition.PNF.GenericExpectedFibreRateExact`, and the previously authored Zipf-family adapter retain independent source ownership. This scoped source-written adaptation is Johl Brown-directed with OpenAI ChatGPT assistance on 28 October 2026. Earlier Ibrahim Monster 3B results are not identified with the statistical carrier and keep separate ownership.

Original Hurwitz recurrence and finite-sum historical authority: [NIST DLMF §25.11](https://dlmf.nist.gov/25.11). No analytic continuation, RH, Navier–Stokes, Monster or RG theorem follows.

## Existing owners reused, not duplicated

1. `DASHI.Statistics.ZipfFamilyFiniteExact`: `mandelbrotDenominator`, `mandelbrotDenominatorNonZero`, `finiteMandelbrotTerm` and the existing unreduced `FiniteFraction` normalizer.
2. `DASHI.Cognition.PNF.GenericExpectedFibreRateExact`: existing `ProbabilityAtom`, `probabilityTotal`, and `normalizedConstantRateIsRate`.
3. `DASHI.Statistics.ZipfIIDTwoDrawAndPNFExact`: the existing normalized finite-rank adapter (not a second record hierarchy).
4. `Data.Rational.Base` / `Data.Rational.Properties`: constructive rational positivity, finite distributivity and reciprocal inverse.

The new module `DASHI/Statistics/ZipfPNFConstructiveNormalizationExact.agda` is a direct statistical sibling and is imported by `DASHI/Statistics/ZipfFamilyEverything.agda` (which is already imported into `DASHI/Everything.agda`). Do not create a new TOE facade, use a master-only Balaban aggregate or touch ESD.

## Mathematical F13 statement and route

For `K=suc n ≥ 1`, `s,q : Nat`, use the original zero-based denominator `d_r=(suc r+q)^s` for `0≤r<K` and the canonical rational `w_r=normalize 1 d_r`. Every `d_r` is positive by the *existing* `mandelbrotDenominatorNonZero` lemma. Use `normalize-pos` to obtain positivity of `w_r`.

Define `Z=Σ_{r<K} w_r`. Induction using `pos+nonNeg⇒pos` establishes `Z>0`. Thus the **mathematically legitimate** reciprocal `1/Z` exists. Construct the actual PNF masses `p_r=w_r * (1/Z)` and discharge the atom's `0≤p_r` proof with positivity of both factors. Their total is proved by the finite distributive identity `Σ(w_r*(1/Z)) = Z*(1/Z)=1`.

Explicit source-written proof terms:
- `rawTermPositive`: positive rational interpretation of the existing source denominator.
- `rawTermMatchesSource`: definitional equality for **individual** unreduced source terms.
- `rawSumNonnegative`, `rawSumPositive`: finite positive total; no admitted normalization premise.
- `inverseNormalizerPositive`: reciprocal retains positivity.
- `scaledSumFactors`: exact distributivity by induction.
- `atomsTotalEqualsScaledSum`: PNF mass fold equals finite scaled rational sum.
- `zipfPNFAtomsNormalize`: PNF mass total exactly 1.
- `finiteZipfPNFAdapter`: existing adapter instantiated by constructed atoms and their proof.
- `zipfPNFConstantExpectation`: apply the *pre-existing* normalized constant expectation theorem.

**Important precise boundary:** `rawTermMatchesSource` is per-rank only. Equality of the **whole unreduced** `Zipf.finiteHurwitz` fraction accumulator with its rational interpretation still needs an Agda fold-homomorphism proof `F05/F13b`. The adapter's `finiteZipfWeightIdentificationPaid` stays `false`. It must not become `true` from numerical parity or naming, and the new module's typechecking is **not verified** in the present environment. The user requested not to prioritize CI, but Agda kernel proof status remains an objective fact.

## Independent exact arithmetic validation

`scripts/zipf_f13_pnf_parity_exact.py` independently reproduces the source `sumFirst/addFraction` unreduced numerator/denominator recurrence and constructs the rational mass vector. It checks a separate common-product numerator `Σ_{r<K} Π_{j≠r}d_j`, which prevents a one-path self-comparison.

`tests/test_zipf_f13_pnf_parity_exact.py` contains nine test functions:
- parameter-grid agreement across support 1..9, shape 0..6, shift 0..5;
- zero-exponent uniform law and zero-shift finite Zipf;
- independent rank/shift/exponent handling;
- exact finite Hurwitz one-step recurrence;
- signed rational constant expected rate;
- IID two-draw collision/mean bridge;
- invalid domain failure, including Python booleans;
- single-type boundary.

**Executed locally:** 9/9 on a materially equivalent standalone copy of the implementation. New committed source and test contents were independently fetched from GitHub; full byte-identical exact-PR-head execution, Agda kernel typecheck and independent empirical corpus validation are **not** claimed. The local acceptance shell includes the new test file; no GitHub Actions result is required for this construction audit.

## Remaining Pareto min-cut

1. Actually typecheck the new and existing three Agda modules with a compatible standard library. If syntax/proof details fail, fix against compiler output. Do not claim proof while source-written only.
2. Prove `interpret (Zipf.addFraction a b) = interpret a + interpret b` given both denominators nonzero; derive `interpret (Zipf.finiteHurwitz K q s) = rawSum K q s` by induction and turn the identification Bool to true only once the theorem is kernel-checked.
3. Expand the same proved finite normalization into the old rank CDF/quantile and expected-vocabulary interfaces only if the carrier map preserves assumptions.
4. Keep Release B's source-identified corpus, full rare tail, heldout model comparison and dependence assumptions separate. A good finite Zipf model fit or the scalar reciprocal proof does not identify a natural-language history, pressure, Fourier phase, zeta zeros or a Monster representation.


## Direct two-rank source-owner reuse (follow-through)

`twoRankP` and `twoRankQ` specialize the constructed support-two mass list. The fold's reverse rank order is explicit. `twoRankPNormalized` derives `p+q≡1ℚ` by rewriting the canonical PNF mass total rather than introducing a second normalizer. `twoRankZipfIIDLaw` instantiates the prior `Adapter.TwoRankIIDLaw` using real nonnegativity proofs; `twoRankZipfCollisionIdentity` applies the **existing** `Adapter.iidTwoDrawMeanPlusCollisionIsTwo` theorem, not an independent recreated result. These terms remain source-written/kernel-pending.

A combined local run of the previous 26 stochastic/completion/stability tests and the 9 F13 arithmetic tests returned **35 passed**. It uses the earlier manually extracted dependency subset and a materially equivalent F13 stand-alone reproduction. Neither full GitHub-head parity nor an Agda compiler result is implied.

A static source review corrected a mistaken initial `cong/sym/trans` import: they now come from `Relation.Binary.PropositionalEquality`, consistent with the repository's existing Agda code.
