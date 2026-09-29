{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedR230SelfExternalRound802Exact where

------------------------------------------------------------------------
-- ROUND802 / SPLIT THE MASKED R230 PHYSICAL CURRENCY INTO SELF + EXTERNAL
--
-- R800 identifies
--
--   B_sep = 8 C_sep,
--
-- where C_sep is the zero-output-safe coherent work against the separated
-- weighted R230 commutator fold.
--
-- R605 proves pointwise, before any fixed-output reindexing,
--
--   FullProductRule = SelfProductRule + ExternalProductRule.
--
-- Attach the R781 fully-separated 0/1 mask to that pointwise identity and fold.
-- Since R798 identifies the masked full product-rule fold with the masked full
-- commutator fold, each nonzero output satisfies exactly
--
--   C_sep(k) = C_self,sep(k) + C_ext,sep(k).
--
-- The zero branch is zero on all three terms, so globally
--
--   C_sep = C_self,sep + C_ext,sep.
--
-- This is precisely the R599 firewall: the external network is retained as an
-- explicit physical channel rather than silently identified with modal energy.
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
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR230SelfExternalNetworkSplitRound605Exact as R605
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact as R798
import DASHI.Physics.Closure.NSTriadKNR650SeparatedBaseGlobalCommutatorRound800Exact as R800

F : C3.RealField _
F = Rational.rationalRealField

module SeparatedR230SelfExternal
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Base =
    R800.GlobalSeparatedBaseCommutator
      physicalSystem S L H velocityTransverse

  module Net = R605.FixedSystem physicalSystem S
  module Id = Base.Id

  cutoff = Base.cutoff

  maskedSelfCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  maskedSelfCell beta with R781.ccTouched beta
  ... | true = C3.complex3Zero F
  ... | false = Net.selfProductRuleCell beta

  maskedExternalCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  maskedExternalCell beta with R781.ccTouched beta
  ... | true = C3.complex3Zero F
  ... | false = Net.externalProductRuleCell beta

  maskedFullSplitsSelfExternal :
    (beta : Physical.PhysicalTriadIncidence) →
    Id.maskedProductCell beta
    ≡ C3.complex3Add
        (maskedSelfCell beta)
        (maskedExternalCell beta)
  maskedFullSplitsSelfExternal beta
    with R781.ccTouched beta
  ... | true =
    sym (Field.complex3AddZeroLeft (C3.complex3Zero F))
  ... | false =
    Net.fullProductRuleCellSplitsSelfExternal beta

  selfFold : Z3.FourierMode → C3.Complex3 F
  selfFold output =
    R224.foldVector maskedSelfCell
      (Output.physicalOutputFiber cutoff output)

  externalFold : Z3.FourierMode → C3.Complex3 F
  externalFold output =
    R224.foldVector maskedExternalCell
      (Output.physicalOutputFiber cutoff output)

  maskedProductFoldSplits :
    (output : Z3.FourierMode) →
    Id.productFold output
    ≡ C3.complex3Add (selfFold output) (externalFold output)
  maskedProductFoldSplits output =
    let
      items = Output.physicalOutputFiber cutoff output

      maskedMeaning :
        R224.foldVector Id.maskedProductCell items
        ≡ C3.complex3Add (selfFold output) (externalFold output)
      maskedMeaning =
        trans
          (Net.foldCongruent
            Id.maskedProductCell
            (λ beta →
              C3.complex3Add
                (maskedSelfCell beta)
                (maskedExternalCell beta))
            maskedFullSplitsSelfExternal
            items)
          (R230.foldAdd maskedSelfCell maskedExternalCell items)
    in
    trans
      (Id.foldMaskedProduct items)
      maskedMeaning

  commutatorFoldSplits :
    (output : Z3.FourierMode) →
    Id.commutatorFold output
    ≡ C3.complex3Add (selfFold output) (externalFold output)
  commutatorFoldSplits output =
    trans
      (sym
        (R798.fixedOutputSeparatedProductRuleIsCommutator
          S Id.velocity Id.forcing cutoff output))
      (maskedProductFoldSplits output)

  outputSelfWork : Z3.FourierMode → ℚ
  outputSelfWork output =
    Work.coherentWork (Id.mixedFold output) (selfFold output)

  outputExternalWork : Z3.FourierMode → ℚ
  outputExternalWork output =
    Work.coherentWork (Id.mixedFold output) (externalFold output)

  selectedSelfWork : Z3.FourierMode → ℚ
  selectedSelfWork output with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputSelfWork output

  selectedExternalWork : Z3.FourierMode → ℚ
  selectedExternalWork output with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputExternalWork output

  outputWorkSplits :
    (output : Z3.FourierMode) →
    Base.outputCommutatorWork output
    ≡ selectedSelfWork output + selectedExternalWork output
  outputWorkSplits output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    trans
      (cong
        (Work.coherentWork (Id.mixedFold output))
        (commutatorFoldSplits output))
      (Work.workAddRight
        (Id.mixedFold output)
        (selfFold output)
        (externalFold output))

  sumSelfWork : List Z3.FourierMode → ℚ
  sumSelfWork [] = 0ℚ
  sumSelfWork (output ∷ rest) =
    selectedSelfWork output + sumSelfWork rest

  sumExternalWork : List Z3.FourierMode → ℚ
  sumExternalWork [] = 0ℚ
  sumExternalWork (output ∷ rest) =
    selectedExternalWork output + sumExternalWork rest

  globalSelfWork : ℚ
  globalSelfWork =
    sumSelfWork
      (Cube.cutoffModes cutoff)

  globalExternalWork : ℚ
  globalExternalWork =
    sumExternalWork
      (Cube.cutoffModes cutoff)

  sumWorkSplits :
    (outputs : List Z3.FourierMode) →
    Base.sumOutputCommutatorWork outputs
    ≡ sumSelfWork outputs + sumExternalWork outputs
  sumWorkSplits [] = refl
  sumWorkSplits (output ∷ rest) =
    trans
      (cong₂ _+_
        (outputWorkSplits output)
        (sumWorkSplits rest))
      (solve
        ( selectedSelfWork output
        ∷ selectedExternalWork output
        ∷ sumSelfWork rest
        ∷ sumExternalWork rest
        ∷ []))

  globalWorkSplitsSelfExternal :
    Base.globalSeparatedCommutatorWork
    ≡ globalSelfWork + globalExternalWork
  globalWorkSplitsSelfExternal =
    sumWorkSplits
      (Cube.cutoffModes cutoff)

round802SeparatedR230WorkSplitsSelfExternal : Bool
round802SeparatedR230WorkSplitsSelfExternal = true

round802ExternalNetworkRetainedExplicitly : Bool
round802ExternalNetworkRetainedExplicitly = true

round802IntroducesEstimate : Bool
round802IntroducesEstimate = false

round802W2Closed : Bool
round802W2Closed = false

round802ClayPromotion : Bool
round802ClayPromotion = false

round802SeparatedR230WorkSplitsSelfExternalIsTrue :
  round802SeparatedR230WorkSplitsSelfExternal ≡ true
round802SeparatedR230WorkSplitsSelfExternalIsTrue = refl

round802ExternalNetworkRetainedExplicitlyIsTrue :
  round802ExternalNetworkRetainedExplicitly ≡ true
round802ExternalNetworkRetainedExplicitlyIsTrue = refl

round802IntroducesEstimateIsFalse :
  round802IntroducesEstimate ≡ false
round802IntroducesEstimateIsFalse = refl

round802W2ClosedIsFalse :
  round802W2Closed ≡ false
round802W2ClosedIsFalse = refl

round802ClayPromotionIsFalse :
  round802ClayPromotion ≡ false
round802ClayPromotionIsFalse = refl
