{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D3ConservedWardChargeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _-_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsLatticeStressWardSliceConservationExact as Ward

------------------------------------------------------------------------
-- D3 / FINITE WARD CHARGE IS ALREADY CONSERVED
--
-- The finite Ward owner proves
--
--   chargeAfter - chargeBefore = 0.
--
-- Over Q this already implies chargeAfter = chargeBefore.  Therefore D3's
-- continuum transport must not be charged with a second finite-time
-- conservation theorem.  Its only genuinely new content is transport in the
-- cutoff/RG index into the completed continuum stress functional.
------------------------------------------------------------------------

differenceZeroImpliesEqual :
  ∀ left right : ℚ →
  left - right ≡ 0ℚ →
  left ≡ right
differenceZeroImpliesEqual left right differenceZero =
  let
    rearranged : left ≡ (left - right) + right
    rearranged = sym (ℚP.+-minus-telescope left right)
  in
  trans rearranged
    (trans
      (cong (λ value → value + right) differenceZero)
      (ℚP.+-identityˡ right))

wardChargeConserved :
  (charge : Ward.LatticeStressWardCharge) →
  Ward.chargeAfter charge ≡ Ward.chargeBefore charge
wardChargeConserved charge =
  differenceZeroImpliesEqual
    (Ward.chargeAfter charge)
    (Ward.chargeBefore charge)
    (Ward.sliceChargeDifferenceZero charge)

------------------------------------------------------------------------
-- Frontier reduction.
------------------------------------------------------------------------

independentFiniteTimeChargeConservationRequiredInD3 : Bool
independentFiniteTimeChargeConservationRequiredInD3 = false

independentFiniteTimeChargeConservationRequiredInD3IsFalse :
  independentFiniteTimeChargeConservationRequiredInD3 ≡ false
independentFiniteTimeChargeConservationRequiredInD3IsFalse = refl

cutoffToContinuumConservedChargeTransportStillPhysical : Bool
cutoffToContinuumConservedChargeTransportStillPhysical = true

cutoffToContinuumConservedChargeTransportStillPhysicalIsTrue :
  cutoffToContinuumConservedChargeTransportStillPhysical ≡ true
cutoffToContinuumConservedChargeTransportStillPhysicalIsTrue = refl

finiteWardChargeConservationCompilerLevel : ProofLevel
finiteWardChargeConservationCompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
