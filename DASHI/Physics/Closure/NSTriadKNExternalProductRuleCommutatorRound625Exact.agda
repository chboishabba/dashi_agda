{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNExternalProductRuleCommutatorRound625Exact where

------------------------------------------------------------------------
-- ROUND625 / EXTERNAL PRODUCT-RULE FORCING -> EXTERNAL MIXED COMMUTATOR
--
-- R605 splits the literal R230 product-rule forcing into selected-self and
-- external-network pieces.  The external cell is
--
--   P+ N_p^ext x P- u_q + P+ u_p x P- N_q^ext.
--
-- R119 proves the exact forcing-slot swap covariance
--
--   N_p^ext(swap tau) = N_q^ext(tau),
--   N_q^ext(swap tau) = N_p^ext(tau).
--
-- Therefore, on the COMPLETE fixed-output fibre, the second external
-- product-rule term reindexes exactly as in R230 and becomes the negative
-- opposite-helicity forcing term.  Hence
--
--   sum ExternalProductRule
--     = sum ( ExternalPlusForceMinusVelocity
--             - ExternalMinusForcePlusVelocity ).
--
-- This is finite signed reindexing only: no norm, absolute value or estimate.
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

  externalPlusForceMinusVelocity :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalPlusForceMinusVelocity tau =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (R95.externalForcingP system tau))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  externalPlusVelocityMinusForce :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalPlusVelocityMinusForce tau =
    Cross.complex3Cross
      (Helical.helicalProjectorPlus E I S
        (Physical.p tau)
        (velocity (Physical.p tau)))
      (Helical.helicalProjectorMinus E I S
        (Physical.q tau)
        (R95.externalForcingQ system tau))

  externalMinusForcePlusVelocity :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalMinusForcePlusVelocity tau =
    Cross.complex3Cross
      (Helical.helicalProjectorMinus E I S
        (Physical.p tau)
        (R95.externalForcingP system tau))
      (Helical.helicalProjectorPlus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  externalCommutatorCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  externalCommutatorCell tau =
    C3.complex3Subtract
      (externalPlusForceMinusVelocity tau)
      (externalMinusForcePlusVelocity tau)

  externalProductRuleMeaning :
    (tau : Physical.PhysicalTriadIncidence) →
    Net.externalProductRuleCell tau
    ≡ C3.complex3Add
        (externalPlusForceMinusVelocity tau)
        (externalPlusVelocityMinusForce tau)
  externalProductRuleMeaning tau = refl

  externalSecondAfterSwapIsNegativeOpposite :
    (tau : Physical.PhysicalTriadIncidence) →
    externalPlusVelocityMinusForce (Symmetry.swapTriad tau)
    ≡ C3.complex3Negate
        (externalMinusForcePlusVelocity tau)
  externalSecondAfterSwapIsNegativeOpposite tau
    rewrite R119.externalForcingQSwapIsP system tau =
    R118.crossAnticommutative
      (Helical.helicalProjectorMinus E I S
        (Physical.p tau)
        (R95.externalForcingP system tau))
      (Helical.helicalProjectorPlus E I S
        (Physical.q tau)
        (velocity (Physical.q tau)))

  fixedOutputExternalSecondReindexesNegative :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector externalPlusVelocityMinusForce
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector
      (λ tau →
        C3.complex3Negate
          (externalMinusForcePlusVelocity tau))
      (Output.physicalOutputFiber cutoff output)
  fixedOutputExternalSecondReindexesNegative cutoff output =
    trans
      (sym
        (R224.foldPermutationInvariant
          externalPlusVelocityMinusForce
          (R224.swapOutputFibrePermutation cutoff output)))
      (trans
        (R224.foldMap
          externalPlusVelocityMinusForce
          Symmetry.swapTriad
          (Output.physicalOutputFiber cutoff output))
        (pointwise (Output.physicalOutputFiber cutoff output)))
    where
    pointwise :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector
        (λ tau →
          externalPlusVelocityMinusForce
            (Symmetry.swapTriad tau))
        items
      ≡
      R224.foldVector
        (λ tau →
          C3.complex3Negate
            (externalMinusForcePlusVelocity tau))
        items
    pointwise [] = refl
    pointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (externalSecondAfterSwapIsNegativeOpposite tau)
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

  fixedOutputExternalProductRuleIsExternalCommutator :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector
      Net.externalProductRuleCell
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector
      externalCommutatorCell
      (Output.physicalOutputFiber cutoff output)
  fixedOutputExternalProductRuleIsExternalCommutator cutoff output =
    let
      fibre = Output.physicalOutputFiber cutoff output
    in
    trans
      (foldCongruent
        Net.externalProductRuleCell
        (λ tau →
          C3.complex3Add
            (externalPlusForceMinusVelocity tau)
            (externalPlusVelocityMinusForce tau))
        externalProductRuleMeaning
        fibre)
      (trans
        (R230.foldAdd
          externalPlusForceMinusVelocity
          externalPlusVelocityMinusForce
          fibre)
        (trans
          (cong₂ C3.complex3Add
            refl
            (fixedOutputExternalSecondReindexesNegative cutoff output))
          (sym
            (R230.foldSubtract
              externalPlusForceMinusVelocity
              externalMinusForcePlusVelocity
              fibre))))

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round625ExternalProductRuleToCommutatorFoldClosed : Bool
round625ExternalProductRuleToCommutatorFoldClosed = true

round625UsesCompleteFixedOutputSwapReindexing : Bool
round625UsesCompleteFixedOutputSwapReindexing = true

round625RequiresLegacyR112WitnessFamily : Bool
round625RequiresLegacyR112WitnessFamily = false

round625IntroducesNormOrAbsoluteValue : Bool
round625IntroducesNormOrAbsoluteValue = false

round625IntroducesEstimate : Bool
round625IntroducesEstimate = false

round625ExternalCommutatorAnalyticPaymentClosed : Bool
round625ExternalCommutatorAnalyticPaymentClosed = false

round625ExternalProductRuleToCommutatorFoldClosedIsTrue :
  round625ExternalProductRuleToCommutatorFoldClosed ≡ true
round625ExternalProductRuleToCommutatorFoldClosedIsTrue = refl

round625UsesCompleteFixedOutputSwapReindexingIsTrue :
  round625UsesCompleteFixedOutputSwapReindexing ≡ true
round625UsesCompleteFixedOutputSwapReindexingIsTrue = refl

round625RequiresLegacyR112WitnessFamilyIsFalse :
  round625RequiresLegacyR112WitnessFamily ≡ false
round625RequiresLegacyR112WitnessFamilyIsFalse = refl

round625IntroducesNormOrAbsoluteValueIsFalse :
  round625IntroducesNormOrAbsoluteValue ≡ false
round625IntroducesNormOrAbsoluteValueIsFalse = refl

round625IntroducesEstimateIsFalse :
  round625IntroducesEstimate ≡ false
round625IntroducesEstimateIsFalse = refl

round625ExternalCommutatorAnalyticPaymentClosedIsFalse :
  round625ExternalCommutatorAnalyticPaymentClosed ≡ false
round625ExternalCommutatorAnalyticPaymentClosedIsFalse = refl
