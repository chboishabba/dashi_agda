{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfZeroSafeSplitRound804Exact where

------------------------------------------------------------------------
-- ROUND804 / SPLIT THE SEPARATED SELF COMMUTATOR INTO R714 ZERO-SAFE + p=0
--
-- R803 puts the separated selected-self channel on the literal R710
-- selfCommutatorCell.
--
-- R714/R720 use the sharper exhaustive carrier
--
--   Self0(tau) = 0          if p_tau = 0,
--              = Self(tau) otherwise.
--
-- A generic PhysicalFiniteComplex3GalerkinSystem does not itself identify the
-- total velocity lookup at zero with the canonical reconstructed mean-zero
-- lookup.  Do not silently erase that distinction.
--
-- Instead split exactly, under the same fully-separated mask:
--
--   Self_sep = Self0_sep + PZeroSelf_sep.
--
-- The first term is definitionally the R714 zero-safe selected-self carrier.
-- The second is supported only where p_tau = 0 and ccTouched tau = false.
--
-- This is a provenance split only.  No estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfCommutatorOrbitRound714Exact as R714
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfCommutatorRound803Exact as R803

module SeparatedSelfZeroSafe
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R803.R802.F)
    (S : Helical.HelicalModeScalars R803.R802.F)
    (L : Helical.PeriodicHelicalProjectorLaws R803.R802.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Sep =
    R803.SeparatedSelfCommutator
      physicalSystem S L H velocityTransverse

  module Single =
    R714.SingleSelfOrbit
      physicalSystem S L H velocityTransverse

  cutoff = Sep.cutoff

  maskedZeroSafeSelf :
    Physical.PhysicalTriadIncidence → C3.Complex3 R803.R802.F
  maskedZeroSafeSelf beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R803.R802.F
  ... | false = Single.singleSelfCommutator beta

  pZeroSelfDefect :
    Physical.PhysicalTriadIncidence → C3.Complex3 R803.R802.F
  pZeroSelfDefect beta
    with R781.ccTouched beta
       | Output.modeEqual (Physical.p beta) Z3.zeroMode
  ... | true | decision = C3.complex3Zero R803.R802.F
  ... | false | true = Sep.Self.selfCommutatorCell beta
  ... | false | false = C3.complex3Zero R803.R802.F

  maskedSelfSplitsZeroSafePlusPZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Sep.maskedSelfCommutator beta
    ≡
    C3.complex3Add
      (maskedZeroSafeSelf beta)
      (pZeroSelfDefect beta)
  maskedSelfSplitsZeroSafePlusPZero beta
    with R781.ccTouched beta
       | Output.modeEqual (Physical.p beta) Z3.zeroMode
  ... | true | decision =
    sym (Field.complex3AddZeroLeft (C3.complex3Zero R803.R802.F))
  ... | false | true =
    sym
      (Field.complex3AddZeroLeft
        (Sep.Self.selfCommutatorCell beta))
  ... | false | false =
    sym
      (Field.complex3AddZeroRight
        (Sep.Self.selfCommutatorCell beta))

  zeroSafeFold : Z3.FourierMode → C3.Complex3 R803.R802.F
  zeroSafeFold output =
    R224.foldVector maskedZeroSafeSelf
      (Output.physicalOutputFiber cutoff output)

  pZeroDefectFold : Z3.FourierMode → C3.Complex3 R803.R802.F
  pZeroDefectFold output =
    R224.foldVector pZeroSelfDefect
      (Output.physicalOutputFiber cutoff output)

  maskedSelfFoldSplits :
    (output : Z3.FourierMode) →
    R224.foldVector Sep.maskedSelfCommutator
      (Output.physicalOutputFiber cutoff output)
    ≡
    C3.complex3Add
      (zeroSafeFold output)
      (pZeroDefectFold output)
  maskedSelfFoldSplits output =
    let
      items = Output.physicalOutputFiber cutoff output
    in
    trans
      (Sep.foldPointwise
        Sep.maskedSelfCommutator
        (λ beta →
          C3.complex3Add
            (maskedZeroSafeSelf beta)
            (pZeroSelfDefect beta))
        maskedSelfSplitsZeroSafePlusPZero
        items)
      (R230.foldAdd
        maskedZeroSafeSelf pZeroSelfDefect items)

  outputZeroSafeWork : Z3.FourierMode → ℚ
  outputZeroSafeWork output =
    Work.coherentWork
      (Sep.Split.Id.mixedFold output)
      (zeroSafeFold output)

  outputPZeroDefectWork : Z3.FourierMode → ℚ
  outputPZeroDefectWork output =
    Work.coherentWork
      (Sep.Split.Id.mixedFold output)
      (pZeroDefectFold output)

  selectedZeroSafeWork : Z3.FourierMode → ℚ
  selectedZeroSafeWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputZeroSafeWork output

  selectedPZeroDefectWork : Z3.FourierMode → ℚ
  selectedPZeroDefectWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputPZeroDefectWork output

  selectedSelfWorkSplits :
    (output : Z3.FourierMode) →
    Sep.selectedMaskedSelfWork output
    ≡ selectedZeroSafeWork output + selectedPZeroDefectWork output
  selectedSelfWorkSplits output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    trans
      (cong
        (Work.coherentWork (Sep.Split.Id.mixedFold output))
        (maskedSelfFoldSplits output))
      (Work.workAddRight
        (Sep.Split.Id.mixedFold output)
        (zeroSafeFold output)
        (pZeroDefectFold output))

  sumZeroSafeWork : List Z3.FourierMode → ℚ
  sumZeroSafeWork [] = 0ℚ
  sumZeroSafeWork (output ∷ rest) =
    selectedZeroSafeWork output + sumZeroSafeWork rest

  sumPZeroDefectWork : List Z3.FourierMode → ℚ
  sumPZeroDefectWork [] = 0ℚ
  sumPZeroDefectWork (output ∷ rest) =
    selectedPZeroDefectWork output + sumPZeroDefectWork rest

  globalZeroSafeSelfWork : ℚ
  globalZeroSafeSelfWork =
    sumZeroSafeWork (Cube.cutoffModes cutoff)

  globalPZeroSelfDefectWork : ℚ
  globalPZeroSelfDefectWork =
    sumPZeroDefectWork (Cube.cutoffModes cutoff)

  globalMaskedSelfWorkSplits :
    Sep.globalMaskedSelfWork
    ≡ globalZeroSafeSelfWork + globalPZeroSelfDefectWork
  globalMaskedSelfWorkSplits =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      Sep.sumMaskedSelfWork outputs
      ≡ sumZeroSafeWork outputs + sumPZeroDefectWork outputs
    go [] = refl
    go (output ∷ rest) =
      trans
        (cong₂ _+_
          (selectedSelfWorkSplits output)
          (go rest))
        (solve
          ( selectedZeroSafeWork output
          ∷ selectedPZeroDefectWork output
          ∷ sumZeroSafeWork rest
          ∷ sumPZeroDefectWork rest
          ∷ []))

round804SeparatedSelfSplitsZeroSafeAndPZero : Bool
round804SeparatedSelfSplitsZeroSafeAndPZero = true

round804ZeroSafeBranchIsLiteralR714Carrier : Bool
round804ZeroSafeBranchIsLiteralR714Carrier = true

round804PZeroDefectExplicit : Bool
round804PZeroDefectExplicit = true

round804IntroducesEstimate : Bool
round804IntroducesEstimate = false

round804PZeroDefectClosed : Bool
round804PZeroDefectClosed = false

round804W2Closed : Bool
round804W2Closed = false

round804ClayPromotion : Bool
round804ClayPromotion = false

round804SeparatedSelfSplitsZeroSafeAndPZeroIsTrue :
  round804SeparatedSelfSplitsZeroSafeAndPZero ≡ true
round804SeparatedSelfSplitsZeroSafeAndPZeroIsTrue = refl

round804ZeroSafeBranchIsLiteralR714CarrierIsTrue :
  round804ZeroSafeBranchIsLiteralR714Carrier ≡ true
round804ZeroSafeBranchIsLiteralR714CarrierIsTrue = refl

round804IntroducesEstimateIsFalse :
  round804IntroducesEstimate ≡ false
round804IntroducesEstimateIsFalse = refl

round804PZeroDefectClosedIsFalse :
  round804PZeroDefectClosed ≡ false
round804PZeroDefectClosedIsFalse = refl

round804W2ClosedIsFalse :
  round804W2Closed ≡ false
round804W2ClosedIsFalse = refl

round804ClayPromotionIsFalse :
  round804ClayPromotion ≡ false
round804ClayPromotionIsFalse = refl
