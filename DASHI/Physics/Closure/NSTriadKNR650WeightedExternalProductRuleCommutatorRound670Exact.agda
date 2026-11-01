{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650WeightedExternalProductRuleCommutatorRound670Exact where

------------------------------------------------------------------------
-- ROUND670 / SWAP-INVARIANT WEIGHTED EXTERNAL PRODUCT RULE -> COMMUTATOR
--
-- R625 proves the unweighted external fixed-output reindexing
--
--   fold ExternalProductRule = fold ExternalCommutator.
--
-- The C1/C2 cross-pollinated route needs the same theorem with the literal
-- spectator/resolvent weight left attached.  For any R294 swap-invariant
-- weight W, define
--
--   wProd(tau) = W(tau) * ExternalProductRule(tau)
--   wComm(tau) = W(tau) * ExternalCommutator(tau).
--
-- The second product-rule term still reindexes through swap(tau), because
-- W(swap tau) = W(tau).  Therefore on the complete fixed-output fibre
--
--   fold wProd = fold wComm.
--
-- This is finite signed reindexing only.  No norm, absolute value, shell
-- estimate, zero-mode deletion, or analytic inequality is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605
import DASHI.Physics.Closure.NSTriadKNExternalProductRuleCommutatorRound625Exact as R625

module WeightedExternal
    {r} {F : C3.RealField r}
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (W : R294.SwapInvariantCellWeight F) where

  system = Field30.finiteSystem physicalSystem

  module Net = R605.FixedSystem physicalSystem S
  module Ext = R625.FixedSystem system S

  weightedProductRule :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedProductRule tau =
    C3.complex3Scale
      (R294.weight W tau)
      (Net.externalProductRuleCell tau)

  weightedFirst :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedFirst tau =
    C3.complex3Scale
      (R294.weight W tau)
      (Ext.externalPlusForceMinusVelocity tau)

  weightedSecond :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedSecond tau =
    C3.complex3Scale
      (R294.weight W tau)
      (Ext.externalPlusVelocityMinusForce tau)

  weightedNegativeOpposite :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedNegativeOpposite tau =
    C3.complex3Scale
      (R294.weight W tau)
      (C3.complex3Negate
        (Ext.externalMinusForcePlusVelocity tau))

  weightedCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedCommutator tau =
    C3.complex3Scale
      (R294.weight W tau)
      (Ext.externalCommutatorCell tau)

  weightedProductRulePointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedProductRule tau
    ≡ C3.complex3Add (weightedFirst tau) (weightedSecond tau)
  weightedProductRulePointwise tau =
    trans
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (Ext.externalProductRuleMeaning tau))
      (R73.complex3ScaleAdd
        (R294.weight W tau)
        (Ext.externalPlusForceMinusVelocity tau)
        (Ext.externalPlusVelocityMinusForce tau))

  weightedSecondAfterSwap :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedSecond (Symmetry.swapTriad tau)
    ≡ weightedNegativeOpposite tau
  weightedSecondAfterSwap tau =
    trans
      (cong
        (λ selectedWeight →
          C3.complex3Scale selectedWeight
            (Ext.externalPlusVelocityMinusForce
              (Symmetry.swapTriad tau)))
        (R294.swapInvariant W tau))
      (cong
        (C3.complex3Scale (R294.weight W tau))
        (Ext.externalSecondAfterSwapIsNegativeOpposite tau))

  weightedCommutatorPointwise :
    (tau : Physical.PhysicalTriadIncidence) →
    weightedCommutator tau
    ≡ C3.complex3Add
        (weightedFirst tau)
        (weightedNegativeOpposite tau)
  weightedCommutatorPointwise tau =
    let
      w = R294.weight W tau
      first = Ext.externalPlusForceMinusVelocity tau
      opposite = Ext.externalMinusForcePlusVelocity tau
    in
    trans
      (R73.complex3ScaleSubtract w first opposite)
      (cong
        (C3.complex3Add (weightedFirst tau))
        (sym (R73.complex3ScaleNegate w opposite)))

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

  weightedSecondReindexesNegative :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector weightedSecond
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector weightedNegativeOpposite
      (Output.physicalOutputFiber cutoff output)
  weightedSecondReindexesNegative cutoff output =
    trans
      (sym
        (R224.foldPermutationInvariant
          weightedSecond
          (R224.swapOutputFibrePermutation cutoff output)))
      (trans
        (R224.foldMap
          weightedSecond
          Symmetry.swapTriad
          (Output.physicalOutputFiber cutoff output))
        (foldCongruent
          (λ tau → weightedSecond (Symmetry.swapTriad tau))
          weightedNegativeOpposite
          weightedSecondAfterSwap
          (Output.physicalOutputFiber cutoff output)))

  fixedOutputWeightedExternalProductRuleIsCommutator :
    (cutoff : Nat) (output : Z3.FourierMode) →
    R224.foldVector weightedProductRule
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector weightedCommutator
      (Output.physicalOutputFiber cutoff output)
  fixedOutputWeightedExternalProductRuleIsCommutator cutoff output =
    let fibre = Output.physicalOutputFiber cutoff output in
    trans
      (foldCongruent
        weightedProductRule
        (λ tau →
          C3.complex3Add
            (weightedFirst tau)
            (weightedSecond tau))
        weightedProductRulePointwise
        fibre)
      (trans
        (R230.foldAdd weightedFirst weightedSecond fibre)
        (trans
          (cong₂ C3.complex3Add
            refl
            (weightedSecondReindexesNegative cutoff output))
          (sym
            (trans
              (foldCongruent
                weightedCommutator
                (λ tau →
                  C3.complex3Add
                    (weightedFirst tau)
                    (weightedNegativeOpposite tau))
                weightedCommutatorPointwise
                fibre)
              (R230.foldAdd
                weightedFirst weightedNegativeOpposite fibre)))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round670WeightedExternalProductRuleCommutatorClosed : Bool
round670WeightedExternalProductRuleCommutatorClosed = true

round670UsesOnlySwapInvariantWeightAndFiniteReindexing : Bool
round670UsesOnlySwapInvariantWeightAndFiniteReindexing = true

round670RequiresLegacyR112WitnessFamily : Bool
round670RequiresLegacyR112WitnessFamily = false

round670IntroducesEstimate : Bool
round670IntroducesEstimate = false

round670ExternalSignedPaymentClosed : Bool
round670ExternalSignedPaymentClosed = false

round670IntroducesNewClayLeaf : Bool
round670IntroducesNewClayLeaf = false

round670ClayPromotion : Bool
round670ClayPromotion = false

round670WeightedExternalProductRuleCommutatorClosedIsTrue :
  round670WeightedExternalProductRuleCommutatorClosed ≡ true
round670WeightedExternalProductRuleCommutatorClosedIsTrue = refl

round670UsesOnlySwapInvariantWeightAndFiniteReindexingIsTrue :
  round670UsesOnlySwapInvariantWeightAndFiniteReindexing ≡ true
round670UsesOnlySwapInvariantWeightAndFiniteReindexingIsTrue = refl

round670RequiresLegacyR112WitnessFamilyIsFalse :
  round670RequiresLegacyR112WitnessFamily ≡ false
round670RequiresLegacyR112WitnessFamilyIsFalse = refl

round670IntroducesEstimateIsFalse :
  round670IntroducesEstimate ≡ false
round670IntroducesEstimateIsFalse = refl

round670ExternalSignedPaymentClosedIsFalse :
  round670ExternalSignedPaymentClosed ≡ false
round670ExternalSignedPaymentClosedIsFalse = refl

round670IntroducesNewClayLeafIsFalse :
  round670IntroducesNewClayLeaf ≡ false
round670IntroducesNewClayLeafIsFalse = refl

round670ClayPromotionIsFalse :
  round670ClayPromotion ≡ false
round670ClayPromotionIsFalse = refl
