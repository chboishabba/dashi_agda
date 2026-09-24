module DASHI.Physics.Closure.NSTriadKNR571PhysicalWeightedSecondMomentEndgameExact where

------------------------------------------------------------------------
-- PERIODIC B / PHYSICAL WEIGHTED SECOND-MOMENT ENDGAME
--
-- The live R571 state side no longer needs a continuous frequency derivative:
-- on the nonzero integer lattice the displacement is at least one, hence the
-- common state-amplitude envelope supplies G2 = 2 G1.  Together with the
-- already-constructed same-displacement A2 sample, the residual B payment can
-- be exposed in the physically useful normal form
--
--       3 E0 * M2  <=  3 E0 * D,
--
-- where M2 is the SAME weighted second moment carried by the literal family and
-- D is whatever dissipation/commutator currency pays M2.
--
-- This owner deliberately does not manufacture M2 <= D.  It makes that one
-- analytic inequality the unique input to the final scaling step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

record PeriodicPhysicalSecondMomentPayment : Set where
  field
    energy : ℚ
    physicalWeightedSecondMoment : ℚ
    dissipationCurrency : ℚ

    energyNonnegative :
      0ℚ ≤ energy

    physicalSecondMomentPaid :
      physicalWeightedSecondMoment ≤ dissipationCurrency

open PeriodicPhysicalSecondMomentPayment public

threeEnergy : PeriodicPhysicalSecondMomentPayment → ℚ
threeEnergy P =
  energy P + energy P + energy P

threeEnergyNonnegative :
  (P : PeriodicPhysicalSecondMomentPayment) →
  0ℚ ≤ threeEnergy P
threeEnergyNonnegative P =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (energyNonnegative P)
      (energyNonnegative P))
    (energyNonnegative P)

scaledPhysicalWeightedSecondMomentPayment :
  (P : PeriodicPhysicalSecondMomentPayment) →
  threeEnergy P * physicalWeightedSecondMoment P
  ≤
  threeEnergy P * dissipationCurrency P
scaledPhysicalWeightedSecondMomentPayment P =
  let
    instance threeEnergyNN =
      nonNegative (threeEnergyNonnegative P)
  in
  ℚP.*-monoˡ-≤-nonNeg
    (threeEnergy P)
    (physicalSecondMomentPaid P)

------------------------------------------------------------------------
-- Machine-readable frontier.
------------------------------------------------------------------------

periodicStateVariationPaidByLatticeGap : Bool
periodicStateVariationPaidByLatticeGap = true

periodicA2UsesSamePhysicalDisplacement : Bool
periodicA2UsesSamePhysicalDisplacement = true

periodicSecondMomentScalingCompilerClosed : Bool
periodicSecondMomentScalingCompilerClosed = true

physicalWeightedSecondMomentPaidFromDissipationHere : Bool
physicalWeightedSecondMomentPaidFromDissipationHere = false

clayPromotion : Bool
clayPromotion = false

periodicStateVariationPaidByLatticeGapIsTrue :
  periodicStateVariationPaidByLatticeGap ≡ true
periodicStateVariationPaidByLatticeGapIsTrue = refl

periodicA2UsesSamePhysicalDisplacementIsTrue :
  periodicA2UsesSamePhysicalDisplacement ≡ true
periodicA2UsesSamePhysicalDisplacementIsTrue = refl

periodicSecondMomentScalingCompilerClosedIsTrue :
  periodicSecondMomentScalingCompilerClosed ≡ true
periodicSecondMomentScalingCompilerClosedIsTrue = refl

physicalWeightedSecondMomentPaidFromDissipationHereIsFalse :
  physicalWeightedSecondMomentPaidFromDissipationHere ≡ false
physicalWeightedSecondMomentPaidFromDissipationHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
