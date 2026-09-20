module DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentSummationExact where

------------------------------------------------------------------------
-- PERIODIC B / SAMPLEWISE PHYSICAL M2 -> FINITE FAMILY PAYMENT
--
-- The preferred R571 compiler has already reduced the signed commutator
-- remainder to the literal finite weighted second moment
--
--     M2 = sum_i w_i d_i^2.
--
-- The next analytic statement should therefore be supplied samplewise on the
-- SAME family whenever possible.  This owner proves that a pointwise physical
-- dissipation payment
--
--     w_i d_i^2 <= D_i
--
-- sums with no cardinality factor:
--
--     M2 <= sum_i D_i.
--
-- No cutoff-uniform estimate is manufactured here.  The theorem is the exact
-- finite aggregation step needed before time integration / R568.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base using (ℚ; _≤_)

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

finitePhysicalSecondMomentPayment :
  (P : PhysicalSecondMomentFamilyPayment) →
  physicalSecondMomentSum P ≤ physicalDissipationSum P
finitePhysicalSecondMomentPayment P =
  let
    go :
      (family : List Moment.PairedSecondMomentSample) →
      ((sample : Moment.PairedSecondMomentSample) →
        sample ∈ family → sample ∈ samples P) →
      Sum.sumBy family Moment.weightedSecondMoment
      ≤ Sum.sumBy family (physicalDissipation P)
    go family included =
      Sum.sumByMonotone family
        Moment.weightedSecondMoment
        (physicalDissipation P)
        (λ sample → samplePayment P sample (included sample
          (let open import Data.List.Membership.Propositional using (here)
           in here refl)))
  in
  Sum.sumByMonotone
    (samples P)
    Moment.weightedSecondMoment
    (physicalDissipation P)
    (λ sample → samplePayment P sample)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

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
