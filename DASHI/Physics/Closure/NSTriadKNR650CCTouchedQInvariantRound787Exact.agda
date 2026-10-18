{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CCTouchedQInvariantRound787Exact where

------------------------------------------------------------------------
-- ROUND787 / ccTouched IS EXACTLY q-ENERGY INVARIANT
--
-- R786 proves the nontrivial direction:
--
--   ccTouched beta = false
--     -> ccTouched (qEnergyLeg beta) = false.
--
-- The corrected R38 action has exact order six.  Therefore the converse is
-- forced: if qEnergyLeg beta were fully separated while beta touched CC,
-- propagate "fully separated" five more q-steps and return to beta, a
-- contradiction.
--
-- Hence the Boolean mask itself is exactly invariant under qEnergyLeg.
-- No estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650FullySeparatedQOrbitCycleRound786Exact as R786

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

qSixSeparated :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched (Orbit.qEnergyLeg beta) ≡ false →
  R781.ccTouched (Orbit.qEnergyLeg (R38.qEnergyLegFive beta)) ≡ false
qSixSeparated beta first =
  R786.fullySeparatedQStep
    (Orbit.qEnergyLeg
      (Orbit.qEnergyLeg
        (Orbit.qEnergyLeg
          (Orbit.qEnergyLeg
            (Orbit.qEnergyLeg beta)))))
    (R786.fullySeparatedQStep
      (Orbit.qEnergyLeg
        (Orbit.qEnergyLeg
          (Orbit.qEnergyLeg
            (Orbit.qEnergyLeg beta))))
      (R786.fullySeparatedQStep
        (Orbit.qEnergyLeg
          (Orbit.qEnergyLeg
            (Orbit.qEnergyLeg beta)))
        (R786.fullySeparatedQStep
          (Orbit.qEnergyLeg
            (Orbit.qEnergyLeg beta))
          (R786.fullySeparatedQStep
            (Orbit.qEnergyLeg beta)
            first))))

ccTouchedQInvariant :
  (beta : Physical.PhysicalTriadIncidence) →
  R781.ccTouched (Orbit.qEnergyLeg beta)
  ≡ R781.ccTouched beta
ccTouchedQInvariant beta
  with R781.ccTouched beta in base
... | false =
  trans
    (R786.fullySeparatedQStep beta base)
    (sym base)
... | true
  with R781.ccTouched (Orbit.qEnergyLeg beta) in next
... | true = refl
... | false =
  ⊥-elim
    (trueNotFalse
      (trans
        (sym base)
        (trans
          (sym
            (cong R781.ccTouched
              (R38.qEnergyLegOrderSixExact beta)))
          (qSixSeparated beta next))))

round787CCTouchedQEnergyInvariant : Bool
round787CCTouchedQEnergyInvariant = true

round787FullySeparatedMaskQEnergyInvariant : Bool
round787FullySeparatedMaskQEnergyInvariant = true

round787DependsOnCorrectedOrderSixOrbit : Bool
round787DependsOnCorrectedOrderSixOrbit = true

round787IntroducesEstimate : Bool
round787IntroducesEstimate = false

round787W2Closed : Bool
round787W2Closed = false

round787ClayPromotion : Bool
round787ClayPromotion = false

round787CCTouchedQEnergyInvariantIsTrue :
  round787CCTouchedQEnergyInvariant ≡ true
round787CCTouchedQEnergyInvariantIsTrue = refl

round787FullySeparatedMaskQEnergyInvariantIsTrue :
  round787FullySeparatedMaskQEnergyInvariant ≡ true
round787FullySeparatedMaskQEnergyInvariantIsTrue = refl

round787DependsOnCorrectedOrderSixOrbitIsTrue :
  round787DependsOnCorrectedOrderSixOrbit ≡ true
round787DependsOnCorrectedOrderSixOrbitIsTrue = refl

round787IntroducesEstimateIsFalse :
  round787IntroducesEstimate ≡ false
round787IntroducesEstimateIsFalse = refl

round787W2ClosedIsFalse :
  round787W2Closed ≡ false
round787W2ClosedIsFalse = refl

round787ClayPromotionIsFalse :
  round787ClayPromotion ≡ false
round787ClayPromotionIsFalse = refl
