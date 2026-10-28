# F13b: concrete positive-denominator rational-addition proof route

**Date:** 2026-10-28. **Canonical owner:** [PR #1275](https://github.com/chboishabba/dashi_agda/pull/1275). **Kernel status:** source-written, Agda compilation not executed. No new postulates, holes, unsafe termination, second probability carrier, ESD modifications, or Monster/RH/NS identification.

## Objective and previous wall

The existing `DASHI.Statistics.ZipfFamilyFiniteExact.Fraction` aliases `DASHI.Core.FiniteUniformProbabilityNormalizationExact.FiniteFraction`, a raw *unreduced* numerator/denominator pair. Its `addFraction` uses the classical cross-product formula. This carrier permits denominator zero, so no total quotient into `ℚ` exists. Previous F13b code correctly restricted the domain by `Nat.NonZero (denominator a)` and exposed the concrete law as the single unpaid `ConcreteAddLaw` field, without constructing an inhabitant.

The new `DASHI/Statistics/ZipfFractionAddRationalBridgeExact.agda` now provides **source-written proof terms** for this specific law, using the already-owned Agda standard-library equivalence between **unnormalized** and **normalized** rationals. Its term `positiveDenominatorAddHomomorphism` is supplied to `concreteAddLawSourceWritten` in the existing `ZipfFractionFoldConditionalExact.agda`, which in turn defines `concreteHurwitzSourceWritten` for every finite count, shift and integer exponent. This is a proof-term completion of the prior **conditional source interface**, *not* an Agda kernel certificate. In particular, the existing `finiteZipfWeightIdentificationPaid=false` flag must remain false pending typechecking.

## Reuse and precise mathematical roots

The new module does not replace or re-prove the library rational algebra. It imports, by existing names:

- `Data.Rational.Base.fromℚᵘ`, `normalize` and `_+_` (canonical reduced rational).
- `Data.Rational.Properties.fromℚᵘ-cong`, `fromℚᵘ-toℚᵘ`, `toℚᵘ-fromℚᵘ`, `toℚᵘ-homo-+`.
- `Data.Rational.Unnormalised.Base.mkℚᵘ`, `_+_` and equivalence `_≃_`.
- `Data.Rational.Unnormalised.Properties.+-cong`, `≃-sym`, `≃-trans`.
- `Data.Nat.Properties.m*n≢0` and pre-existing source fraction arithmetic, finite Hurwitz fold and valid denominator witnesses.

Primary documentation for library authors' work:
- https://agda.github.io/agda-stdlib/master/Data.Rational.Base.html
- https://agda.github.io/agda-stdlib/master/Data.Rational.Properties.html
- https://agda.github.io/agda-stdlib/master/Data.Rational.Unnormalised.Base.html
- https://agda.github.io/agda-stdlib/master/Data.Rational.Unnormalised.Properties.html

Historical finite rank laws belong to Estoup, Zipf, Mandelbrot and Hurwitz. Classical rational field is elementary historical mathematics. The source-written adapter is Johl Brown-directed with OpenAI ChatGPT assistance, 2026-10-28; the separate earlier PNF/SSSP owners and Ibrahim Monster 3B representation claims retain their own independent authorship.

## Constructive proof ladder

1. `validRawFraction` embeds each **positive-denominator** source fraction into the standard library's already-owned raw rational `ℚᵘ`. Its zero-denominator case is eliminated by the explicit `Nat.NonZero` proof (not an unchecked Boolean). No illegal quotient is introduced.
2. `validReducedFraction` interprets that same source pair as `normalize numerator denominator`.
3. `rawToReduced` identifies `fromℚᵘ (validRawFraction a)` with the normalized quotient. It uses definitional reduction for a source fraction with denominator `suc d`.
4. `rawFractionAddPreserved` expresses the **literal existing source** cross-product numerator and product denominator as the standard-library raw rational sum; source proof uses the positive constructor and definitional arithmetic.
5. `fromRawPreservesAddition` uses the already-proved library equivalence `toℚᵘ-fromℚᵘ`, raw `+-cong`, `toℚᵘ-homo-+`, and `fromℚᵘ-toℚᵘ` to transport raw addition across normalization. It does not invent an extra group or arithmetic law.
6. `positiveDenominatorAddHomomorphism` composes steps 3–5 and returns the `ConcreteAddLaw` equality for all raw `a,b` **with nonzero denominator witnesses**.
7. In `ZipfFractionFoldConditionalExact`, `concreteAddLawSourceWritten` supplies this actual source term, and `concreteHurwitzSourceWritten` applies the prior generic finite fold induction. The theorem target is exactly:

```
normalize (numerator (finiteHurwitz K q s))
          (denominator (finiteHurwitz K q s))
      == sum_{r=0}^{K-1} normalize 1 ((r+q+1)^s)
```

The separate F13 PNF atom normalizer consumes this finite rational sum. **Only after Agda typechecks the complete import graph** may the previous adapter's source-identity `false` be changed to a kernel-verified flag. Its current `false` value is deliberate.

## Checks performed, source provenance and remaining wall

An independent local Python `Fraction` check passed **4096** finite numerator/positive-denominator addition pairs (8 numerator values × 8 positive denominators for each side) and verified that reducing the source `addFraction` cross-product agrees with the library-style reduced rational. Another **784** independent finite Hurwitz accumulator checks covered counts `0..13`, shifts `0..6`, integer exponents `0..7`, including the count-zero identity and exponent-zero uniform case. No arithmetic check failed.

The focused regression `tests/test_zipf_f13b_raw_rational_proof_exact.py` contains these exact checks and tests the source import/proof-status boundary. It is registered in `scripts/check_zipf_family_acceptance.sh`. The actual Agda source was committed via GitHub and read back, but **no local Agda compiler exists**. The imported standard-library theorem names were independently verified against the published Agda docs; precise tactic elaboration and definitional `refl` compatibility remain to be checked by the compiler.

Thus the previous F13b **missing proof construction** has been replaced by a **concrete source-written proof**, not by a postulate or mock certificate. The next real wall is Agda kernel verification and any required compiler-guided repairs, together with separate H08 all-count and S24 proof formalization. Do not claim that this finishes any of the 27 empirical/diagnostic topics or proves the unbounded analytic Hurwitz-zeta continuation.

## Independent max-cut ordering

P0: compile `ZipfFractionAddRationalBridgeExact.agda`, `ZipfFractionFoldConditionalExact.agda` and `ZipfPNFConstructiveNormalizationExact.agda` on the repository's compatible Agda/stdlib. Resolve any constructor/implicit proof elaboration errors without broad new abstractions.

P1: replace the adapter's identifier-only `finiteZipfWeightIdentificationPaid=false` with a *typed verified evidence bridge* ONLY when the prior theorem has typechecked; preserve existing historical authors and evidence tiers.

P2: formalize the existing constructive S24 pair-switch/HLP chain and H08 all-count sharp histories over the already-owned probability, finite-statistics and chronology carriers; use the 27 subject contracts to avoid falsely proving empirical power-laws.


## Agda toolchain compatibility clarification

The repository's existing `scripts/run_agda29_parallel_check.sh` targets Agda **2.9** and defaults `AGDA_STDLIB_REF=experimental` (the local standard-library source path may override it). The existing `dashi-agda.agda-lib` also depends on `standard-library`, `dchott-agda`, `bishop` and `cubical-0.9`.

The public `agda-stdlib/master` pages document the **specific theorem names used by this proof**; however, public latest docs are **not** a verification that the repository's actual experimental pin elaborates those terms, nor that the full dchott/bishop/cubical import graph compiles. A legitimate final receipt must include the exact Agda binary version, stdlib commit, invocation and successful kernel result. Until then, the proof remains source-written.

The appropriate existing local workflow is the repository's `scripts/run_agda29_parallel_check.sh` with a focused target `DASHI/Statistics/ZipfFractionAddRationalBridgeExact.agda`, followed by `ZipfFractionFoldConditionalExact.agda` and `ZipfFamilyEverything.agda`. Do not edit any protected ESD path, import master-only owner modules onto this diverged branch without verifying their actual availability, or use CI green as a substitute for interpreting concrete proof types.


## Subsequent proof elaboration hardening

A static review caught that the initial `rawFractionAddPreserved` branch used `refl` for the raw source-to-`ℚᵘ` addition equality. Although correct arithmetically, relying on definitional equality of the natural-to-integer embedding is needlessly fragile (and can fail with the standard library's sign/magnitude representation).

The proof term has now been strengthened to use **the already-owned integer embedding homomorphism lemmas** `Data.Integer.Properties.pos-+` and `pos-*` explicitly, combined with `cong₂`. This relates `+(n*e+m*d)` to `(+n)*(+e) + (+m)*(+d)` without asking the kernel to infer the arithmetic conversion by normalization alone. The positive denominator product is unchanged. The two impossible zero-denominator cases still use absurd patterns. The proof remains kernel-pending; this is compiler-risk reduction, not a compiler receipt.
