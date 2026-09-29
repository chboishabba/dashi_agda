{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- Minimal rational Haar-integration laws needed by the CMP119 stress lane.
------------------------------------------------------------------------

record RationalFiniteMeasureIntegrationLaws
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    haarIntegralCongruent :
      ∀ left right →
      (∀ configuration → left configuration ≡ right configuration) →
      Physical.haarIntegral measure left
      ≡ Physical.haarIntegral measure right

    haarIntegralZero :
      Physical.haarIntegral measure (λ _ → 0ℚ) ≡ 0ℚ

    haarIntegralAdd :
      ∀ left right →
      Physical.haarIntegral measure
        (λ configuration → left configuration + right configuration)
      ≡
      Physical.haarIntegral measure left
      + Physical.haarIntegral measure right

open RationalFiniteMeasureIntegrationLaws public

haarIntegralFourAdd :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : RationalFiniteMeasureIntegrationLaws measure)
    f0 f1 f2 f3 →
  Physical.haarIntegral measure
    (λ configuration →
      (f0 configuration + f1 configuration)
      + (f2 configuration + f3 configuration))
  ≡
  (Physical.haarIntegral measure f0
    + Physical.haarIntegral measure f1)
  +
  (Physical.haarIntegral measure f2
    + Physical.haarIntegral measure f3)
haarIntegralFourAdd {measure = measure} laws f0 f1 f2 f3 =
  trans
    (haarIntegralAdd laws
      (λ x → f0 x + f1 x)
      (λ x → f2 x + f3 x))
    (cong₂ _+_
      (haarIntegralAdd laws f0 f1)
      (haarIntegralAdd laws f2 f3))
