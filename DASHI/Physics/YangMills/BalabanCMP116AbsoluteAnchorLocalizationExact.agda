{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116AbsoluteAnchorLocalizationExact where

------------------------------------------------------------------------
-- ABSOLUTE ANCHOR + COMPARISON -> ABSOLUTE SELECTED LOCALIZATION
--
-- R385 pays the difficult selected/reference comparison route.  R386 correctly
-- observes that a difference bound alone cannot control an absolute response.
-- This module proves the exact missing analysis step once an independently
-- controlled reference response is supplied:
--
--   |S - R| <= C_cmp * q^d
--   |R|     <= C_ref * q^d
--   --------------------------------
--   |S|     <= (C_cmp + C_ref) * q^d.
--
-- This is ordinary rational absolute-value analysis; it introduces no source
-- authority and makes the remaining CMP116 application debt an explicit
-- reference-anchor estimate rather than another opaque "localization" field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record AbsoluteAnchorLocalizationData : Set₁ where
  field
    selected reference : Nat → ℚ
    comparisonAmplitude referenceAmplitude ratio : ℚ

    comparisonAmplitudeNonnegative : 0ℚ ≤ comparisonAmplitude
    referenceAmplitudeNonnegative : 0ℚ ≤ referenceAmplitude
    ratioNonnegative : 0ℚ ≤ ratio

    selectedReferenceDifferenceBound : ∀ depth →
      ∣ selected depth - reference depth ∣
      ≤ comparisonAmplitude * Power.rationalPower ratio depth

    referenceAbsoluteBound : ∀ depth →
      ∣ reference depth ∣
      ≤ referenceAmplitude * Power.rationalPower ratio depth

open AbsoluteAnchorLocalizationData public

absoluteSplit : ∀ selectedValue referenceValue →
  ∣ selectedValue ∣
  ≤ ∣ selectedValue - referenceValue ∣ + ∣ referenceValue ∣
absoluteSplit selectedValue referenceValue =
  subst
    (λ value →
      ∣ value ∣
      ≤ ∣ selectedValue - referenceValue ∣ + ∣ referenceValue ∣)
    (decomposition selectedValue referenceValue)
    (ℚP.∣p+q∣≤∣p∣+∣q∣
      (selectedValue - referenceValue) referenceValue)
  where
  decomposition : ∀ s r → s ≡ (s - r) + r
  decomposition = ℚRing.solve-∀

sumAmplitudeFactor : ∀ a b factor →
  a * factor + b * factor ≡ (a + b) * factor
sumAmplitudeFactor = ℚRing.solve-∀

selectedAbsoluteBound : (dataSet : AbsoluteAnchorLocalizationData) → ∀ depth →
  ∣ selected dataSet depth ∣
  ≤ (comparisonAmplitude dataSet + referenceAmplitude dataSet)
      * Power.rationalPower (ratio dataSet) depth
selectedAbsoluteBound dataSet depth =
  let
    split = absoluteSplit
      (selected dataSet depth) (reference dataSet depth)
    cmp = selectedReferenceDifferenceBound dataSet depth
    ref = referenceAbsoluteBound dataSet depth
    summed =
      ℚP.+-mono-≤ cmp ref
  in
  subst
    (λ upper → ∣ selected dataSet depth ∣ ≤ upper)
    (sumAmplitudeFactor
      (comparisonAmplitude dataSet)
      (referenceAmplitude dataSet)
      (Power.rationalPower (ratio dataSet) depth))
    (ℚP.≤-trans split summed)

absoluteAnchorLocalizationCompilerLevel : ProofLevel
absoluteAnchorLocalizationCompilerLevel = machineChecked
