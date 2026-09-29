{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedExternalCommutatorRound809Exact where

------------------------------------------------------------------------
-- ROUND809 / LIFT R625 THROUGH THE FULLY-SEPARATED MASK
--
-- R802 leaves the separated external channel as coherent work against the
-- masked R605 external product-rule fold.
--
-- R625 proves on each complete fixed-output fibre:
--
--   sum ExternalProductRule = sum ExternalCommutator,
--
-- by p/q-swap reindexing.  R781 proves the fully-separated selector is swap
-- invariant, so exactly the same finite reindexing survives with the selector.
--
-- Therefore the R802 external work is moved, without estimate, onto the
-- literal R625 external commutator carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNExternalProductRuleCommutatorRound625Exact as R625
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230SelfExternalRound802Exact as R802

module SeparatedExternalCommutator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R802.F)
    (S : Helical.HelicalModeScalars R802.F)
    (L : Helical.PeriodicHelicalProjectorLaws R802.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Split =
    R802.SeparatedR230SelfExternal
      physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem

  module Ext = R625.FixedSystem system S

  cutoff = Split.cutoff

  maskedFirst :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedFirst beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Ext.externalPlusForceMinusVelocity beta

  maskedSecond :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedSecond beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Ext.externalPlusVelocityMinusForce beta

  maskedOpposite :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedOpposite beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Ext.externalMinusForcePlusVelocity beta

  maskedExternalCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedExternalCommutator beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Ext.externalCommutatorCell beta

  maskedExternalProductMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    Split.maskedExternalCell beta
    ≡ C3.complex3Add (maskedFirst beta) (maskedSecond beta)
  maskedExternalProductMeaning beta
    with R781.ccTouched beta
  ... | true =
    sym (Field.complex3AddZeroLeft (C3.complex3Zero R802.F))
  ... | false =
    Ext.externalProductRuleMeaning beta

  maskedSecondAfterSwapIsNegativeOpposite :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedSecond (Symmetry.swapTriad beta)
    ≡ C3.complex3Negate (maskedOpposite beta)
  maskedSecondAfterSwapIsNegativeOpposite beta
    rewrite R781.ccTouchedSwapInvariant beta
    with R781.ccTouched beta
  ... | true =
    sym
      (DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact.complex3NegateZero
        {F = R802.F})
  ... | false =
    Ext.externalSecondAfterSwapIsNegativeOpposite beta

  foldPointwise :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 R802.F) →
    ((beta : Physical.PhysicalTriadIncidence) → left beta ≡ right beta) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldPointwise left right pointwise [] = refl
  foldPointwise left right pointwise (beta ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise beta)
      (foldPointwise left right pointwise rest)

  fixedOutputMaskedSecondReindexesNegative :
    (output : Z3.FourierMode) →
    R224.foldVector maskedSecond
      (Output.physicalOutputFiber cutoff output)
    ≡
    R224.foldVector
      (λ beta → C3.complex3Negate (maskedOpposite beta))
      (Output.physicalOutputFiber cutoff output)
  fixedOutputMaskedSecondReindexesNegative output =
    let
      items = Output.physicalOutputFiber cutoff output
    in
    trans
      (sym
        (R224.foldPermutationInvariant
          maskedSecond
          (R224.swapOutputFibrePermutation cutoff output)))
      (trans
        (R224.foldMap maskedSecond Symmetry.swapTriad items)
        (foldPointwise
          (λ beta → maskedSecond (Symmetry.swapTriad beta))
          (λ beta → C3.complex3Negate (maskedOpposite beta))
          maskedSecondAfterSwapIsNegativeOpposite
          items))

  maskedExternalCommutatorMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedExternalCommutator beta
    ≡ C3.complex3Subtract (maskedFirst beta) (maskedOpposite beta)
  maskedExternalCommutatorMeaning beta
    with R781.ccTouched beta
  ... | true =
    sym
      (DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact.complex3SubtractSelf
        (C3.complex3Zero R802.F))
  ... | false = refl

  fixedOutputMaskedExternalProductIsCommutator :
    (output : Z3.FourierMode) →
    Split.externalFold output
    ≡
    R224.foldVector maskedExternalCommutator
      (Output.physicalOutputFiber cutoff output)
  fixedOutputMaskedExternalProductIsCommutator output =
    let
      items = Output.physicalOutputFiber cutoff output

      split :
        Split.externalFold output
        ≡
        C3.complex3Add
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedSecond items)
      split =
        trans
          (foldPointwise
            Split.maskedExternalCell
            (λ beta → C3.complex3Add (maskedFirst beta) (maskedSecond beta))
            maskedExternalProductMeaning
            items)
          (R230.foldAdd maskedFirst maskedSecond items)

      reindexed :
        C3.complex3Add
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedSecond items)
        ≡
        C3.complex3Subtract
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedOpposite items)
      reindexed =
        trans
          (cong₂ C3.complex3Add
            refl
            (fixedOutputMaskedSecondReindexesNegative output))
          (sym
            (R230.foldSubtract maskedFirst maskedOpposite items))

      commMeaning :
        C3.complex3Subtract
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedOpposite items)
        ≡
        R224.foldVector maskedExternalCommutator items
      commMeaning =
        trans
          (R230.foldSubtract maskedFirst maskedOpposite items)
          (sym
            (foldPointwise
              maskedExternalCommutator
              (λ beta →
                C3.complex3Subtract
                  (maskedFirst beta)
                  (maskedOpposite beta))
              maskedExternalCommutatorMeaning
              items))
    in
    trans split (trans reindexed commMeaning)

  outputMaskedExternalWork : Z3.FourierMode → ℚ
  outputMaskedExternalWork output =
    Work.coherentWork
      (Split.Id.mixedFold output)
      (R224.foldVector maskedExternalCommutator
        (Output.physicalOutputFiber cutoff output))

  selectedMaskedExternalWork : Z3.FourierMode → ℚ
  selectedMaskedExternalWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputMaskedExternalWork output

  selectedExternalWorkIsCommutatorWork :
    (output : Z3.FourierMode) →
    Split.selectedExternalWork output
    ≡ selectedMaskedExternalWork output
  selectedExternalWorkIsCommutatorWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    cong
      (Work.coherentWork (Split.Id.mixedFold output))
      (fixedOutputMaskedExternalProductIsCommutator output)

  sumMaskedExternalWork : List Z3.FourierMode → ℚ
  sumMaskedExternalWork [] = 0ℚ
  sumMaskedExternalWork (output ∷ rest) =
    selectedMaskedExternalWork output + sumMaskedExternalWork rest

  globalMaskedExternalWork : ℚ
  globalMaskedExternalWork =
    sumMaskedExternalWork (Cube.cutoffModes cutoff)

  globalExternalWorkIsMaskedCommutatorWork :
    Split.globalExternalWork ≡ globalMaskedExternalWork
  globalExternalWorkIsMaskedCommutatorWork =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      Split.sumExternalWork outputs ≡ sumMaskedExternalWork outputs
    go [] = refl
    go (output ∷ rest) =
      cong₂ _+_
        (selectedExternalWorkIsCommutatorWork output)
        (go rest)

round809SeparatedExternalProductRuleToCommutatorClosed : Bool
round809SeparatedExternalProductRuleToCommutatorClosed = true

round809SeparatedExternalWorkOnR625Carrier : Bool
round809SeparatedExternalWorkOnR625Carrier = true

round809IntroducesEstimate : Bool
round809IntroducesEstimate = false

round809W2Closed : Bool
round809W2Closed = false

round809ClayPromotion : Bool
round809ClayPromotion = false

round809SeparatedExternalProductRuleToCommutatorClosedIsTrue :
  round809SeparatedExternalProductRuleToCommutatorClosed ≡ true
round809SeparatedExternalProductRuleToCommutatorClosedIsTrue = refl

round809SeparatedExternalWorkOnR625CarrierIsTrue :
  round809SeparatedExternalWorkOnR625Carrier ≡ true
round809SeparatedExternalWorkOnR625CarrierIsTrue = refl

round809IntroducesEstimateIsFalse :
  round809IntroducesEstimate ≡ false
round809IntroducesEstimateIsFalse = refl

round809W2ClosedIsFalse :
  round809W2Closed ≡ false
round809W2ClosedIsFalse = refl

round809ClayPromotionIsFalse :
  round809ClayPromotion ≡ false
round809ClayPromotionIsFalse = refl
