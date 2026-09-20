module DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentSummationExact where

------------------------------------------------------------------------
-- PERIODIC B / SAMPLEWISE PHYSICAL M2 -> FINITE FAMILY PAYMENT
--
-- A pointwise payment on the SAME finite R571 family,
--
--     w_i d_i^2 <= D_i,
--
-- sums with no cardinality factor:
--
--     sum_i w_i d_i^2 <= sum_i D_i.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNLuoFiniteCenteredCommutatorBudgetExact as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact as Moment

record PhysicalSecondMomentFamilyPayment : Set₁ where
  field
    samples : List Moment.PairedSecondMomentSample
    physicalDissipation : Moment.PairedSecondMomentSample → ℚ

    samplePayment :
      (sample : Moment.PairedSecondMomentSample) →
      sample ∈ samples →
      Moment.weightedSecondMoment sample
      ≤ physicalDissipation sample

open PhysicalSecondMomentFamilyPayment public

physicalSecondMomentSum :
  PhysicalSecondMomentFamilyPayment → ℚ
physicalSecondMomentSum P =
  Sum.sumBy (samples P) Moment.weightedSecondMoment

physicalDissipationSum :
  PhysicalSecondMomentFamilyPayment → ℚ
physicalDissipationSum P =
  Sum.sumBy (samples P) (physicalDissipation P)

sumPhysicalPaymentOn :
  (P : PhysicalSecondMomentFamilyPayment) →
  (family : List Moment.PairedSecondMomentSample) →
  ((sample : Moment.PairedSecondMomentSample) →
    sample ∈ family → sample ∈ samples P) →
  Sum.sumBy family Moment.weightedSecondMoment
  ≤ Sum.sumBy family (physicalDissipation P)
sumPhysicalPaymentOn P [] included = ℚP.≤-refl
sumPhysicalPaymentOn P (sample ∷ rest) included =
  ℚP.+-mono-≤
    (samplePayment P sample (included sample (here refl)))
    (sumPhysicalPaymentOn P rest
      (λ other member → included other (there member)))

finitePhysicalSecondMomentPayment :
  (P : PhysicalSecondMomentFamilyPayment) →
  physicalSecondMomentSum P ≤ physicalDissipationSum P
finitePhysicalSecondMomentPayment P =
  sumPhysicalPaymentOn P (samples P) (λ sample member → member)

finiteM2AggregationAddsCardinalityLoss : Bool
finiteM2AggregationAddsCardinalityLoss = false

samplewisePhysicalM2PaymentSuffices : Bool
samplewisePhysicalM2PaymentSuffices = true

samplewisePhysicalM2TheoremConstructedHere : Bool
samplewisePhysicalM2TheoremConstructedHere = false

cutoffUniformSpacetimePaymentConstructedHere : Bool
cutoffUniformSpacetimePaymentConstructedHere = false

clayPromotion : Bool
clayPromotion = false

samplewisePhysicalM2PaymentSufficesIsTrue :
  samplewisePhysicalM2PaymentSuffices ≡ true
samplewisePhysicalM2PaymentSufficesIsTrue = refl

finiteM2AggregationAddsCardinalityLossIsFalse :
  finiteM2AggregationAddsCardinalityLoss ≡ false
finiteM2AggregationAddsCardinalityLossIsFalse = refl
