{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfCommutatorRound803Exact where

------------------------------------------------------------------------
-- ROUND803 / LIFT R710 THROUGH THE FULLY-SEPARATED MASK
--
-- R802 leaves the separated selected-self channel as the coherent work against
-- the masked R605 self product-rule fold.
--
-- R710 proves on a complete fixed-output fibre:
--
--   sum SelfProductRule = sum SelfCommutator,
--
-- using only the physical p/q swap reindexing.  R781 proves the modern
-- fullySeparated mask is exactly swap invariant, so that reindexing survives
-- with the mask attached.
--
-- Therefore, output by output:
--
--   SelfProduct_sep(k) = SelfCommutator_sep(k),
--
-- and the R802 global selected-self work can be rewritten on the same literal
-- selected-self commutator carrier used by R714/R719/R720.
--
-- No estimate, norm, absolute value, or zero-mode deletion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650SelfProductRuleCommutatorRound710Exact as R710
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230SelfExternalRound802Exact as R802

module SeparatedSelfCommutator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem
      R802.F)
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

  module Self =
    R710.FixedSystem (Field30.finiteSystem physicalSystem) S

  cutoff = Split.cutoff

  maskedFirst :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedFirst beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Self.selfPlusForceMinusVelocity beta

  maskedSecond :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedSecond beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Self.selfPlusVelocityMinusForce beta

  maskedOpposite :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedOpposite beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Self.selfMinusForcePlusVelocity beta

  maskedSelfCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 R802.F
  maskedSelfCommutator beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R802.F
  ... | false = Self.selfCommutatorCell beta

  maskedSelfProductMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    Split.maskedSelfCell beta
    ≡ C3.complex3Add (maskedFirst beta) (maskedSecond beta)
  maskedSelfProductMeaning beta
    with R781.ccTouched beta
  ... | true =
    sym (Field.complex3AddZeroLeft (C3.complex3Zero R802.F))
  ... | false =
    Self.selfProductRuleMeaning beta

  maskedSecondAfterSwapIsNegativeOpposite :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedSecond (Symmetry.swapTriad beta)
    ≡ C3.complex3Negate (maskedOpposite beta)
  maskedSecondAfterSwapIsNegativeOpposite beta
    rewrite R781.ccTouchedSwapInvariant beta
    with R781.ccTouched beta
  ... | true =
    sym (R225.complex3NegateZero {F = R802.F})
  ... | false =
    Self.selfSecondAfterSwapIsNegativeOpposite beta

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

  maskedSelfCommutatorMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedSelfCommutator beta
    ≡ C3.complex3Subtract (maskedFirst beta) (maskedOpposite beta)
  maskedSelfCommutatorMeaning beta
    with R781.ccTouched beta
  ... | true =
    sym (R106.complex3SubtractSelf (C3.complex3Zero R802.F))
  ... | false = refl

  fixedOutputMaskedSelfProductIsCommutator :
    (output : Z3.FourierMode) →
    Split.selfFold output
    ≡
    R224.foldVector maskedSelfCommutator
      (Output.physicalOutputFiber cutoff output)
  fixedOutputMaskedSelfProductIsCommutator output =
    let
      items = Output.physicalOutputFiber cutoff output

      productSplit :
        Split.selfFold output
        ≡
        C3.complex3Add
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedSecond items)
      productSplit =
        trans
          (foldPointwise
            Split.maskedSelfCell
            (λ beta → C3.complex3Add (maskedFirst beta) (maskedSecond beta))
            maskedSelfProductMeaning
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

      commutatorMeaning :
        C3.complex3Subtract
          (R224.foldVector maskedFirst items)
          (R224.foldVector maskedOpposite items)
        ≡
        R224.foldVector maskedSelfCommutator items
      commutatorMeaning =
        trans
          (R230.foldSubtract maskedFirst maskedOpposite items)
          (sym
            (foldPointwise
              maskedSelfCommutator
              (λ beta →
                C3.complex3Subtract
                  (maskedFirst beta)
                  (maskedOpposite beta))
              maskedSelfCommutatorMeaning
              items))
    in
    trans productSplit
      (trans reindexed commutatorMeaning)

  outputMaskedSelfWork : Z3.FourierMode → ℚ
  outputMaskedSelfWork output =
    Work.coherentWork
      (Split.Id.mixedFold output)
      (R224.foldVector maskedSelfCommutator
        (Output.physicalOutputFiber cutoff output))

  selectedMaskedSelfWork : Z3.FourierMode → ℚ
  selectedMaskedSelfWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputMaskedSelfWork output

  selectedSelfWorkIsCommutatorWork :
    (output : Z3.FourierMode) →
    Split.selectedSelfWork output ≡ selectedMaskedSelfWork output
  selectedSelfWorkIsCommutatorWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    cong
      (Work.coherentWork (Split.Id.mixedFold output))
      (fixedOutputMaskedSelfProductIsCommutator output)

  sumMaskedSelfWork : List Z3.FourierMode → ℚ
  sumMaskedSelfWork [] = 0ℚ
  sumMaskedSelfWork (output ∷ rest) =
    selectedMaskedSelfWork output + sumMaskedSelfWork rest

  globalMaskedSelfWork : ℚ
  globalMaskedSelfWork =
    sumMaskedSelfWork (Cube.cutoffModes cutoff)

  globalSelfWorkIsMaskedCommutatorWork :
    Split.globalSelfWork ≡ globalMaskedSelfWork
  globalSelfWorkIsMaskedCommutatorWork =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      Split.sumSelfWork outputs ≡ sumMaskedSelfWork outputs
    go [] = refl
    go (output ∷ rest) =
      cong₂ _+_
        (selectedSelfWorkIsCommutatorWork output)
        (go rest)

round803SeparatedSelfProductRuleToCommutatorClosed : Bool
round803SeparatedSelfProductRuleToCommutatorClosed = true

round803SeparatedSelfWorkOnR710Carrier : Bool
round803SeparatedSelfWorkOnR710Carrier = true

round803IntroducesEstimate : Bool
round803IntroducesEstimate = false

round803W2Closed : Bool
round803W2Closed = false

round803ClayPromotion : Bool
round803ClayPromotion = false

round803SeparatedSelfProductRuleToCommutatorClosedIsTrue :
  round803SeparatedSelfProductRuleToCommutatorClosed ≡ true
round803SeparatedSelfProductRuleToCommutatorClosedIsTrue = refl

round803SeparatedSelfWorkOnR710CarrierIsTrue :
  round803SeparatedSelfWorkOnR710Carrier ≡ true
round803SeparatedSelfWorkOnR710CarrierIsTrue = refl

round803IntroducesEstimateIsFalse :
  round803IntroducesEstimate ≡ false
round803IntroducesEstimateIsFalse = refl

round803W2ClosedIsFalse :
  round803W2Closed ≡ false
round803W2ClosedIsFalse = refl

round803ClayPromotionIsFalse :
  round803ClayPromotion ≡ false
round803ClayPromotionIsFalse = refl
