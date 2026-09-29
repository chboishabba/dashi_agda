{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfProductRuleCommutatorRound710Exact where

------------------------------------------------------------------------
-- ROUND710 / SELECTED-SELF PRODUCT RULE -> SELECTED-SELF MIXED COMMUTATOR
--
-- R605 defines the selected-self product-rule cell
--
--   P+ N_p^self x P- u_q + P+ u_p x P- N_q^self.
--
-- R119 already proves exact swap covariance
--
--   N_p^self(swap tau) = N_q^self(tau),
--   N_q^self(swap tau) = N_p^self(tau).
--
-- Therefore on the COMPLETE fixed-output fibre the second product-rule term
-- reindexes to the negative opposite-helicity first-slot term, exactly as in
-- R230/R625.  Hence
--
--   sum SelfProductRule = sum SelfCommutator.
--
-- No estimate, norm, absolute value, or shell count appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeSelectedSwapAntisymmetryRound118Exact as R118
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact as R119
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605

module FixedSystem
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F) where

  velocity = Audit.velocity system
  module Net = R605.FixedSystem system S

  selfPlusForceMinusVelocity :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfPlusForceMinusVelocity tau =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (R95.selfForcingP system tau))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  selfPlusVelocityMinusForce :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfPlusVelocityMinusForce tau =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (velocity (Physical.p tau)))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (R95.selfForcingQ system tau))

  selfMinusForcePlusVelocity :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfMinusForcePlusVelocity tau =
    Cross.complex3Cross
      (Helical.helicalProjectorMinus E I S
        (Physical.p tau)
        (R95.selfForcingP system tau))
      (Helical.helicalProjectorPlus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  selfCommutatorCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  selfCommutatorCell tau =
    C3.complex3Subtract
      (selfPlusForceMinusVelocity tau)
      (selfMinusForcePlusVelocity tau)

  selfProductRuleMeaning :
    (tau : Physical.PhysicalTriadIncidence) →
    Net.selfProductRuleCell tau
    ≡ C3.complex3Add
        (selfPlusForceMinusVelocity tau)
        (selfPlusVelocityMinusForce tau)
  selfProductRuleMeaning tau = refl

  selfSecondAfterSwapIsNegativeOpposite :
    (tau : Physical.PhysicalTriadIncidence) →
    selfPlusVelocityMinusForce (Symmetry.swapTriad tau)
    ≡ C3.complex3Negate
        (selfMinusForcePlusVelocity tau)
  selfSecondAfterSwapIsNegativeOpposite tau
    rewrite R119.selfForcingQSwapIsP system tau =
    R118.crossAnticommutative
      (Helical.helicalProjectorMinus E I S
        (Physical.p tau)
        (R95.selfForcingP system tau))
      (Helical.helicalProjectorPlus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  fixedOutputSelfSecondReindexesNegative :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector selfPlusVelocityMinusForce
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector
      (λ tau →
        C3.complex3Negate
          (selfMinusForcePlusVelocity tau))
      (Output.physicalOutputFiber cutoff output)
  fixedOutputSelfSecondReindexesNegative cutoff output =
    trans
      (sym
        (R224.foldPermutationInvariant
          selfPlusVelocityMinusForce
          (R224.swapOutputFibrePermutation cutoff output)))
      (trans
        (R224.foldMap
          selfPlusVelocityMinusForce
          Symmetry.swapTriad
          (Output.physicalOutputFiber cutoff output))
        (pointwise (Output.physicalOutputFiber cutoff output)))
    where
    pointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector
        (λ tau →
          selfPlusVelocityMinusForce
            (Symmetry.swapTriad tau))
        items
      ≡
      R224.foldVector
        (λ tau →
          C3.complex3Negate
            (selfMinusForcePlusVelocity tau))
        items
    pointwise [] = refl
    pointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (selfSecondAfterSwapIsNegativeOpposite tau)
        (pointwise rest)

  foldCongruent :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldCongruent left right pointwise [] = refl
  foldCongruent left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldCongruent left right pointwise rest)

  fixedOutputSelfProductRuleIsSelfCommutator :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector
      Net.selfProductRuleCell
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector
      selfCommutatorCell
      (Output.physicalOutputFiber cutoff output)
  fixedOutputSelfProductRuleIsSelfCommutator cutoff output =
    let
      fibre = Output.physicalOutputFiber cutoff output
    in
    trans
      (foldCongruent
        Net.selfProductRuleCell
        (λ tau →
          C3.complex3Add
            (selfPlusForceMinusVelocity tau)
            (selfPlusVelocityMinusForce tau))
        selfProductRuleMeaning
        fibre)
      (trans
        (R230.foldAdd
          selfPlusForceMinusVelocity
          selfPlusVelocityMinusForce
          fibre)
        (trans
          (cong₂ C3.complex3Add
            refl
            (fixedOutputSelfSecondReindexesNegative cutoff output))
          (sym
            (R230.foldSubtract
              selfPlusForceMinusVelocity
              selfMinusForcePlusVelocity
              fibre))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round710SelfProductRuleToCommutatorFoldClosed : Bool
round710SelfProductRuleToCommutatorFoldClosed = true

round710UsesCompleteFixedOutputSwapReindexing : Bool
round710UsesCompleteFixedOutputSwapReindexing = true

round710IntroducesEstimate : Bool
round710IntroducesEstimate = false

round710SelfCommutatorCutoffUniformPaymentClosed : Bool
round710SelfCommutatorCutoffUniformPaymentClosed = false

round710ClayPromotion : Bool
round710ClayPromotion = false

round710SelfProductRuleToCommutatorFoldClosedIsTrue :
  round710SelfProductRuleToCommutatorFoldClosed ≡ true
round710SelfProductRuleToCommutatorFoldClosedIsTrue = refl

round710UsesCompleteFixedOutputSwapReindexingIsTrue :
  round710UsesCompleteFixedOutputSwapReindexing ≡ true
round710UsesCompleteFixedOutputSwapReindexingIsTrue = refl

round710IntroducesEstimateIsFalse :
  round710IntroducesEstimate ≡ false
round710IntroducesEstimateIsFalse = refl

round710ClayPromotionIsFalse :
  round710ClayPromotion ≡ false
round710ClayPromotionIsFalse = refl
