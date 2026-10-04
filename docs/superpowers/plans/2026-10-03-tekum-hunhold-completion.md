# Hunhold Tekum Paper Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the remaining general mathematical obligations from Hunhold’s Tekum paper on PR #1083: balanced positional reconstruction, concrete fixed-width `int_n`, source-word decoding, Propositions 2–5, no-double-rounding, and general wheel parity.

**Architecture:** Keep one theorem spine: positional balanced-integer semantics first, then instantiate the fixed-width arithmetic and source parser, then prove all paper propositions against the existing canonical `ℚ` decoder. Do not use cardinality as a substitute for positional injectivity, and keep special values in a source-faithful ordered wrapper rather than forcing NaR/infinity into `ℚ`.

**Tech Stack:** Agda + stdlib `Data.Integer`, `Data.Rational`, `Data.Vec`, existing DASHI balanced-ternary/A003462/Tekum owners, static Python regression.

**Spec:** `docs/superpowers/specs/2026-10-03-tekum-paper-max-cut-design.md`

## Global Constraints

- Reuse `DASHI.Algebra.Trit` and `BalancedTernaryIntegerExact.eval`; do not create a second positional evaluator.
- Reuse the existing A003462 maximum-magnitude owner and finite-product/cardinality owners.
- Ordinary finite Tekum semantics must use the existing canonical `ℚ` decoder; machine floating point is not semantic authority.
- NaR/infinity remain distinct constructors; no silent rational coercion.
- No `{!!}`, `postulate`, termination escapes, or placeholder theorem fields in new canonical owners.
- Preserve source attribution; DASHI cross-pollination must remain explicitly separate from Hunhold’s claims.
- Use TDD: add/load-bearing regression surface first, verify it fails for the absent theorem, then implement the theorem, then run focused + full available checks.

## Review Focus

1. **Negative balanced integers:** reconstruction must choose the balanced remainder correctly for `-1 mod 3`, not reuse an unsigned remainder convention.
2. **Width-zero / width-one boundaries:** centered interval and reconstruction must remain total where the source convention permits the width.
3. **Special-value ordering:** Prop. 4 must not derive NaR/infinity ordering from `ℚ`; special branches must be explicit.
4. **Rounding ties:** Prop. 5 must encode exactly the source tie convention and must not prove a stronger unique-nearest claim when ties are permitted.
5. **Field-length dependence:** source-word parsing must prove split/join lengths rather than trust metadata when regime changes exponent/fraction allocation.

---

### Task 1: Positional integer recurrence and injectivity

**Files:**
- Create: `DASHI/Algebra/BalancedTernaryPositionalInjectiveExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: `BalancedTernaryIntegerExact.eval`, `toInteger`, `Trit.inv`.
- Produces: `evalIntegerCons`, `balancedRemainderDistinct`, `toIntegerInjective`.

- [ ] **Step 1: Write the failing regression**
  Add the new owner and theorem names to `scripts/check_tekum_balanced_ternary_static.py`, with concrete checks that `[-1]`, `[0]`, `[+1]`, `[-1,+1]`, `[0,+1]`, `[+1,+1]` have the expected integer evaluations and that `toIntegerInjective` is present.

- [ ] **Step 2: Verify RED**
  Run `python scripts/check_tekum_balanced_ternary_static.py` and confirm failure because `BalancedTernaryPositionalInjectiveExact.agda` / `toIntegerInjective` do not yet exist.

- [ ] **Step 3: Implement the positional proof owner**
  Define the recurrence theorem
  `evalIntegerCons : toInteger (eval (t ∷ ts)) ≡ digitInteger t + 3 * toInteger (eval ts)`
  and prove the three head-digit residue classes modulo 3 are disjoint. Use that to prove
  `toIntegerInjective : ∀ {n} {x y : Vec Trit n} → toInteger (eval x) ≡ toInteger (eval y) → x ≡ y`.

- [ ] **Step 4: Verify GREEN**
  Run the static regression and focused Agda check for the new owner; then run the repository’s available Tekum/Agda check suite.

- [ ] **Step 5: Commit**
  `git commit -am "Balanced ternary: prove positional evaluator injective"`

### Task 2: A003462 range and centered reconstruction

**Files:**
- Create: `DASHI/Algebra/BalancedTernaryCenteredReconstructionExact.agda`
- Create: `DASHI/Algebra/BalancedTernaryCenteredBijectionExact.agda`
- Modify: `DASHI/Algebra/BalancedTernaryA003462BridgeExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: `toIntegerInjective`, A003462 `balancedTernaryMaxMagnitude`, finite `Trit^n` carrier/cardinality.
- Produces: `CenteredInteger n`, `decodeCentered`, `decodeEncodeCentered`, `encodeDecodeCentered`, `toIntegerWithinCenteredRange`, `balancedTernaryCenteredBijection`.

- [ ] **Step 1: Write failing regression fixtures**
  Add width-1, width-2, width-3 endpoint/middle reconstruction cases and require both roundtrip theorem names.

- [ ] **Step 2: Verify RED**
  Confirm the regression fails because centered reconstruction is absent.

- [ ] **Step 3: Implement centered interval and decoder**
  Define a bounded signed carrier whose proof field is `-A_n ≤ z ≤ A_n`. Reconstruct by the unique balanced remainder in `{-1,0,+1}` modulo 3 and recurse on the exact quotient. Prove the result remains in the width-`n` centered interval.

- [ ] **Step 4: Prove range and both roundtrips**
  Prove every word evaluates inside `[-A_n,A_n]`, decoding an encoded word returns the word, and encoding a centered integer returns the original centered integer. Export the explicit equivalence theorem rather than relying on cardinality.

- [ ] **Step 5: Verify GREEN**
  Run static + focused Agda + available full suite.

- [ ] **Step 6: Commit**
  `git commit -am "Balanced ternary: construct centered positional bijection"`

### Task 3: Concrete fixed-width Hunhold `int_n`

**Files:**
- Create: `DASHI/ComputerScience/TekumFixedWidthBalancedArithmeticExact.agda`
- Modify: `DASHI/ComputerScience/TekumAnchorArithmeticExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: centered bijection + `invertWord`.
- Produces: `tekumBalancedArithmetic : (n : Nat) → FixedWidthBalancedArithmetic n`, `wrapCentered`, `addWord`, `subtractWord`, `modulusWord`, `concreteAnchor`, `concreteAnchorNegationInvariant`.

- [ ] **Step 1: Write failing arithmetic regressions**
  Require one- and two-trit wraparound examples, additive inverse examples, modulus-negation symmetry, and concrete anchor evaluation.

- [ ] **Step 2: Verify RED**
  Confirm absence of `tekumBalancedArithmetic` fails the regression.

- [ ] **Step 3: Implement wrapping through the `3^n` residue class**
  Define wrapping via centered reconstruction of the residue represented modulo `3^n`; do not use host overflow. Define word add/subtract/negation and source modulus.

- [ ] **Step 4: Instantiate `FixedWidthBalancedArithmetic`**
  Prove `modulus (negate x) ≡ modulus x` and define the concrete source anchor with the all-positive word.

- [ ] **Step 5: Verify GREEN + commit**
  Run focused + full available checks, then commit `Tekum: instantiate fixed-width balanced arithmetic`.

### Task 4: Source-word parser into the canonical rational semantics

**Files:**
- Create: `DASHI/ComputerScience/TekumSourceWordDecodeExact.agda`
- Create: `DASHI/ComputerScience/TekumSourceWordRoundTripExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: concrete anchor, `TekumRegimeExponentExact`, `TekumSpecialValuesExact`, `TekumExactTriadicSemanticsExact.ordinaryRational`.
- Produces: `parseTekumWord`, `joinParsedTekumWord`, `parseJoin`, `joinParse`, `decodeFiniteTekumWord`, dependent field-length equalities.

- [ ] **Step 1: Write failing parser regressions**
  Require representative central/outer positive and negative regimes, plus NaR/zero/infinity classification and split/join roundtrips.

- [ ] **Step 2: Verify RED**
  Confirm parser theorem names are absent.

- [ ] **Step 3: Implement dependent parse**
  Parse anchor → regime → exponent/fraction lengths → field words, with length equalities carried in the result. Convert balanced exponent/fraction fields through the centered positional decoder into `OrdinaryTekum`.

- [ ] **Step 4: Prove split/join roundtrips and define source-word value**
  `decodeFiniteTekumWord` must delegate ordinary values to `ordinaryRational`; specials remain special constructors.

- [ ] **Step 5: Verify GREEN + commit**
  Run focused + full checks, then commit `Tekum: connect source words to exact rational decoder`.

### Task 5: Hunhold Proposition 2 and Proposition 3

**Files:**
- Create: `DASHI/ComputerScience/TekumNoRedundantEncodingExact.agda`
- Create: `DASHI/ComputerScience/TekumSourceNegationExact.agda`
- Modify: `DASHI/ComputerScience/TekumUniquenessExact.agda`
- Modify: `DASHI/ComputerScience/TekumNegationExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: source parser, centered positional injectivity, exact `ℚ` decoder, existing sign/denominator symmetry.
- Produces: `fractionStrictHalfBound`, `ordinaryExponentIntervalsDisjoint`, `tekumDecodeInjective`, `parseNegatedWord`, `tekumDecodeNegation`.

- [ ] **Step 1: Write failing theorem regressions**
  Require Prop. 2 source-word injectivity and Prop. 3 source-word negation; include ordinary and special fixtures.

- [ ] **Step 2: Verify RED**
  Confirm failures because the final source-level theorems are absent.

- [ ] **Step 3: Prove ordinary magnitude interval separation**
  Prove `-1/2 < f < 1/2` from the centered fraction bound, then the source interval `1/2 * 3^e < |T| < 3/2 * 3^e`; prove adjacent exponent intervals intersect only at excluded endpoints.

- [ ] **Step 4: Prove Prop. 2**
  Split specials/ordinary, recover sign + exponent + fraction, then use parser roundtrip and balanced positional injectivity to recover the exact word.

- [ ] **Step 5: Prove Prop. 3**
  Show parsing the inverted word preserves anchor/regime allocation and flips external sign; transport through `ordinaryRational`, with explicit special cases.

- [ ] **Step 6: Verify GREEN + commit**
  Run focused + full checks, then commit `Tekum: close source uniqueness and negation propositions`.

### Task 6: Hunhold Proposition 4 total order

**Files:**
- Create: `DASHI/ComputerScience/TekumSourceOrderExact.agda`
- Modify: `DASHI/ComputerScience/TekumMonotonicityExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: centered integer code, parser, Prop. 2, canonical rational order.
- Produces: `TekumOrderedValue`, `_<_`, `integerCodeOrderAgreesWithTekum`, source Prop. 4 theorem.

- [ ] **Step 1: Write failing order regressions**
  Exercise negative→zero→positive boundaries, adjacent exponent boundaries, adjacent same-exponent fractions, infinity, and the source’s NaR placement.

- [ ] **Step 2: Verify RED**
  Confirm Prop. 4 theorem absent.

- [ ] **Step 3: Implement source-faithful ordered wrapper**
  Ordinary branch delegates to `ℚ`; special ordering is explicit and source-derived. Do not infer special order from rational values.

- [ ] **Step 4: Prove integer-code monotonicity**
  Case split by source region/regime, reduce ordinary same-region order to exponent/fraction rational order, and prove the code-order theorem.

- [ ] **Step 5: Verify GREEN + commit**
  Run checks and commit `Tekum: prove source integer-code monotonicity`.

### Task 7: Hunhold Proposition 5 nearest rounding

**Files:**
- Create: `DASHI/ComputerScience/TekumNearestRoundingExact.agda`
- Modify: `DASHI/ComputerScience/TekumTruncationRoundingExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: source parser, exact rational decode, concrete anchor inverse, Prop. 4 order, existing `truncateTwo` structural map.
- Produces: `LowerPrecisionCandidate`, `tekumDistance`, `Nearest`, `truncateIsNearest`, tie theorem matching source convention.

- [ ] **Step 1: Write failing nearest-rounding regressions**
  Add small-width fixtures for exact hits, below/above midpoint, and source-permitted ties. Require the general `truncateIsNearest` theorem.

- [ ] **Step 2: Verify RED**
  Confirm nearest theorem absent.

- [ ] **Step 3: Define lower-precision candidate semantics and exact distance**
  Use rational absolute difference for ordinary finite values and explicit source rules for specials.

- [ ] **Step 4: Prove coarse-cell geometry**
  Show truncating the two low anchor trits selects the containing lower-precision cell representative and bounds the discarded contribution by half the next spacing.

- [ ] **Step 5: Prove global nearest property**
  Use Prop. 4 to show all non-neighbouring candidates are farther; discharge neighbouring midpoint/tie cases exactly according to source convention.

- [ ] **Step 6: Verify GREEN + commit**
  Run checks and commit `Tekum: prove truncation is nearest rounding`.

### Task 8: Numerical no-double-rounding corollary

**Files:**
- Create: `DASHI/ComputerScience/TekumNoDoubleRoundingExact.agda`
- Modify: `DASHI/ComputerScience/TekumPrecisionCompositionExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: `truncateIsNearest` + existing structural two-step composition.
- Produces: `nearestRoundComposition`, source no-double-rounding theorem.

- [ ] **Step 1: Write failing regression** requiring the numerical no-double-rounding theorem and small-width equality fixtures.
- [ ] **Step 2: Verify RED**.
- [ ] **Step 3: Prove the numerical corollary** by transporting the already-proved structural equality through source-word decode and Prop. 5 nearest semantics; do not build a second rounding algorithm.
- [ ] **Step 4: Verify GREEN + commit** with focused + full checks.

### Task 9: General wheel parity theorem

**Files:**
- Create: `DASHI/ComputerScience/TekumWheelParityGeneralExact.agda`
- Modify: `DASHI/ComputerScience/TekumWheelStateParityExact.agda`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: existing width examples + stdlib modular arithmetic.
- Produces: `pow3Mod4Parity`, `wheelQuarterIntegralityIffEvenWidth`.

- [ ] **Step 1: Write failing parity regression** requiring widths 0–8 plus the general iff theorem.
- [ ] **Step 2: Verify RED**.
- [ ] **Step 3: Prove `3^n mod 4` alternates `1,3` with parity** and derive `4 ∣ (3^n - 5) ↔ Even n`, formulated without truncated Nat subtraction where necessary.
- [ ] **Step 4: Verify GREEN + commit**.

### Task 10: Capstone, documentation, and verification

**Files:**
- Modify: `DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda`
- Modify: `Docs/TekumBalancedTernaryFormalisation.md`
- Modify: `scripts/check_tekum_balanced_ternary_static.py`

**Interfaces:**
- Consumes: Tasks 1–9.
- Produces: capstone fields marking exactly which original-paper theorems are paid and which source/hardware obligations remain.

- [ ] **Step 1: Make capstone regression fail** by requiring the new canonical theorem names.
- [ ] **Step 2: Update capstone imports/boundary** so positional bijection, concrete `int_n`, source parser, Props. 2–5, numerical no-double-rounding, and general wheel parity are `true` only because theorem owners exist.
- [ ] **Step 3: Update documentation** with theorem statements, owner paths, and explicit original-paper vs DASHI-derived boundaries.
- [ ] **Step 4: Run verification**: static checker, focused Agda modules, available repository-wide Agda/test commands, and exact-head PR workflow/status check. Report every failure by name rather than claiming a green suite from partial checks.
- [ ] **Step 5: Commit** `Tekum: close Hunhold paper theorem capstone`.
