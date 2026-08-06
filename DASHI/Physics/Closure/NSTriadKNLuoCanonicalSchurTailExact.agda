module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSchurTailExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Upgrade the existing cutoff-uniform Schur bound to explicit tail control.
-- For every starting index and every finite tail length,
--
--   sum_{n=0}^N r^(start+n)
--     = r^start sum_{n=0}^N r^n.
--
-- Consequently the canonical low-shell and gap tails are bounded by
--
--   (4/3)(1/4)^start,
--   (32/31)(1/32)^start,
--
-- and the corresponding two-dimensional strips by
--
--   (128/93)(1/4)^start,
--   (128/93)(1/32)^start.
--
-- These are quantitative finite-extension bounds required for an infinite
-- resonant-fibre Cauchy argument; unlike a uniform prefix bound, they decay
-- with the starting cutoff.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst; sym; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum

powAdd :
  (ratio : ℚ) →
  (left right : Nat) →
  Geo.pow ratio (left + right)
  ≡ Geo.pow ratio left * Geo.pow ratio right
powAdd ratio zero right =
  solve (Geo.pow ratio right ∷ [])
powAdd ratio (suc left) right
  rewrite powAdd ratio left right =
  solve
    ( ratio
    ∷ Geo.pow ratio left
    ∷ Geo.pow ratio right
    ∷ []
    )

sumToCong :
  (left right : Nat → ℚ) →
  (cutoff : Nat) →
  ((index : Nat) → left index ≡ right index) →
  Sum.sumTo left cutoff ≡ Sum.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise
  rewrite pointwise (suc cutoff)
        | sumToCong left right cutoff pointwise = refl

shiftedPowerSum : ℚ → Nat → Nat → ℚ
shiftedPowerSum ratio start cutoff =
  Sum.sumTo
    (λ offset → Geo.pow ratio (start + offset))
    cutoff

shiftedPowerSumFactorization :
  (ratio : ℚ) →
  (start cutoff : Nat) →
  shiftedPowerSum ratio start cutoff
  ≡ Geo.pow ratio start * Geo.partialSum ratio cutoff
shiftedPowerSumFactorization ratio start cutoff =
  trans
    (sumToCong
      (λ offset → Geo.pow ratio (start + offset))
      (λ offset → Geo.pow ratio start * Geo.pow ratio offset)
      cutoff
      (powAdd ratio start))
    (trans
      (Sum.scaleSum (Geo.pow ratio start) (Geo.pow ratio) cutoff)
      (cong
        (Geo.pow ratio start *_)
        (Sum.powerSumMeaning ratio cutoff)))

shiftedTailBound :
  (ratio bound : ℚ) →
  0ℚ ≤ ratio →
  ((cutoff : Nat) → Geo.partialSum ratio cutoff ≤ bound) →
  (start cutoff : Nat) →
  shiftedPowerSum ratio start cutoff
  ≤ Geo.pow ratio start * bound
shiftedTailBound ratio bound ratioNonnegative prefixBound start cutoff =
  subst
    (λ left → left ≤ Geo.pow ratio start * bound)
    (sym (shiftedPowerSumFactorization ratio start cutoff))
    (let instance startPowerIsNonnegative =
       nonNegative (Geo.powNonnegative ratio start ratioNonnegative)
     in
     ℚₚ.*-monoˡ-≤-nonNeg
       (Geo.pow ratio start)
       (prefixBound cutoff))

quarterShiftedTailBound :
  (start cutoff : Nat) →
  shiftedPowerSum Geo.quarter start cutoff
  ≤ Geo.pow Geo.quarter start * Geo.fourThirds
quarterShiftedTailBound =
  shiftedTailBound
    Geo.quarter
    Geo.fourThirds
    Geo.quarterNonnegative
    Geo.quarterPartialSumBound

thirtySecondShiftedTailBound :
  (start cutoff : Nat) →
  shiftedPowerSum Geo.thirtySecond start cutoff
  ≤ Geo.pow Geo.thirtySecond start * Geo.thirtyTwoThirtyFirsts
thirtySecondShiftedTailBound =
  shiftedTailBound
    Geo.thirtySecond
    Geo.thirtyTwoThirtyFirsts
    Geo.thirtySecondNonnegative
    Geo.thirtySecondPartialSumBound

lowExteriorStrip : Nat → Nat → Nat → ℚ
lowExteriorStrip start lowTailCutoff gapCutoff =
  shiftedPowerSum Geo.quarter start lowTailCutoff
  * Geo.partialSum Geo.thirtySecond gapCutoff

gapExteriorStrip : Nat → Nat → Nat → ℚ
gapExteriorStrip start gapTailCutoff lowCutoff =
  Geo.partialSum Geo.quarter lowCutoff
  * shiftedPowerSum Geo.thirtySecond start gapTailCutoff

lowExteriorStripBound :
  (start lowTailCutoff gapCutoff : Nat) →
  lowExteriorStrip start lowTailCutoff gapCutoff
  ≤ Geo.pow Geo.quarter start
      * Geo.oneTwentyEightNinetyThirds
lowExteriorStripBound start lowTailCutoff gapCutoff =
  let
    gapPrefixNonnegative =
      Geo.partialSumNonnegative
        Geo.thirtySecond gapCutoff Geo.thirtySecondNonnegative

    first :
      lowExteriorStrip start lowTailCutoff gapCutoff
      ≤ (Geo.pow Geo.quarter start * Geo.fourThirds)
          * Geo.partialSum Geo.thirtySecond gapCutoff
    first =
      let instance gapPrefixIsNonnegative =
        nonNegative gapPrefixNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Geo.partialSum Geo.thirtySecond gapCutoff)
        (quarterShiftedTailBound start lowTailCutoff)

    leftFactorNonnegative :
      0ℚ ≤ Geo.pow Geo.quarter start * Geo.fourThirds
    leftFactorNonnegative =
      let
        instance
          powerIsNonnegative = nonNegative
            (Geo.powNonnegative
              Geo.quarter start Geo.quarterNonnegative)
          constantIsNonnegative = nonNegative Geo.fourThirdsNonnegative
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (Geo.pow Geo.quarter start)
              Geo.fourThirds
      in
      ℚₚ.nonNegative⁻¹
        (Geo.pow Geo.quarter start * Geo.fourThirds)

    second :
      (Geo.pow Geo.quarter start * Geo.fourThirds)
        * Geo.partialSum Geo.thirtySecond gapCutoff
      ≤ (Geo.pow Geo.quarter start * Geo.fourThirds)
        * Geo.thirtyTwoThirtyFirsts
    second =
      let instance factorIsNonnegative =
        nonNegative leftFactorNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        (Geo.pow Geo.quarter start * Geo.fourThirds)
        (Geo.thirtySecondPartialSumBound gapCutoff)

    targetMeaning :
      (Geo.pow Geo.quarter start * Geo.fourThirds)
        * Geo.thirtyTwoThirtyFirsts
      ≡ Geo.pow Geo.quarter start
        * Geo.oneTwentyEightNinetyThirds
    targetMeaning =
      begin
        (Geo.pow Geo.quarter start * Geo.fourThirds)
          * Geo.thirtyTwoThirtyFirsts
      ≡⟨ solve
          ( Geo.pow Geo.quarter start
          ∷ Geo.fourThirds
          ∷ Geo.thirtyTwoThirtyFirsts
          ∷ []
          ) ⟩
        Geo.pow Geo.quarter start
          * (Geo.fourThirds * Geo.thirtyTwoThirtyFirsts)
      ≡⟨ cong
          (Geo.pow Geo.quarter start *_)
          Geo.productConstantIdentity ⟩
        Geo.pow Geo.quarter start
          * Geo.oneTwentyEightNinetyThirds
      ∎
  in
  ℚₚ.≤-trans first
    (subst
      (λ upper →
        (Geo.pow Geo.quarter start * Geo.fourThirds)
          * Geo.partialSum Geo.thirtySecond gapCutoff
        ≤ upper)
      targetMeaning
      second)

gapExteriorStripBound :
  (start gapTailCutoff lowCutoff : Nat) →
  gapExteriorStrip start gapTailCutoff lowCutoff
  ≤ Geo.pow Geo.thirtySecond start
      * Geo.oneTwentyEightNinetyThirds
gapExteriorStripBound start gapTailCutoff lowCutoff =
  let
    tailNonnegative =
      Sum.sumToNonnegative
        (λ offset → Geo.pow Geo.thirtySecond (start + offset))
        gapTailCutoff
        (λ offset →
          Geo.powNonnegative
            Geo.thirtySecond
            (start + offset)
            Geo.thirtySecondNonnegative)

    first :
      gapExteriorStrip start gapTailCutoff lowCutoff
      ≤ Geo.fourThirds
        * shiftedPowerSum Geo.thirtySecond start gapTailCutoff
    first =
      let instance tailIsNonnegative = nonNegative tailNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (shiftedPowerSum Geo.thirtySecond start gapTailCutoff)
        (Geo.quarterPartialSumBound lowCutoff)

    second :
      Geo.fourThirds
        * shiftedPowerSum Geo.thirtySecond start gapTailCutoff
      ≤ Geo.fourThirds
        * (Geo.pow Geo.thirtySecond start
          * Geo.thirtyTwoThirtyFirsts)
    second =
      let instance fourThirdsIsNonnegative =
        nonNegative Geo.fourThirdsNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        Geo.fourThirds
        (thirtySecondShiftedTailBound start gapTailCutoff)

    targetMeaning :
      Geo.fourThirds
        * (Geo.pow Geo.thirtySecond start
          * Geo.thirtyTwoThirtyFirsts)
      ≡ Geo.pow Geo.thirtySecond start
        * Geo.oneTwentyEightNinetyThirds
    targetMeaning =
      begin
        Geo.fourThirds
          * (Geo.pow Geo.thirtySecond start
            * Geo.thirtyTwoThirtyFirsts)
      ≡⟨ solve
          ( Geo.pow Geo.thirtySecond start
          ∷ Geo.fourThirds
          ∷ Geo.thirtyTwoThirtyFirsts
          ∷ []
          ) ⟩
        Geo.pow Geo.thirtySecond start
          * (Geo.fourThirds * Geo.thirtyTwoThirtyFirsts)
      ≡⟨ cong
          (Geo.pow Geo.thirtySecond start *_)
          Geo.productConstantIdentity ⟩
        Geo.pow Geo.thirtySecond start
          * Geo.oneTwentyEightNinetyThirds
      ∎
  in
  ℚₚ.≤-trans first
    (subst
      (λ upper →
        Geo.fourThirds
          * shiftedPowerSum Geo.thirtySecond start gapTailCutoff
        ≤ upper)
      targetMeaning
      second)

canonicalSchurQuantitativeTailClosed : Bool
canonicalSchurQuantitativeTailClosed = true

canonicalLowAndGapExteriorStripsDecay : Bool
canonicalLowAndGapExteriorStripsDecay = true

canonicalSchurQuantitativeTailClosedIsTrue :
  canonicalSchurQuantitativeTailClosed ≡ true
canonicalSchurQuantitativeTailClosedIsTrue = refl

canonicalLowAndGapExteriorStripsDecayIsTrue :
  canonicalLowAndGapExteriorStripsDecay ≡ true
canonicalLowAndGapExteriorStripsDecayIsTrue = refl
