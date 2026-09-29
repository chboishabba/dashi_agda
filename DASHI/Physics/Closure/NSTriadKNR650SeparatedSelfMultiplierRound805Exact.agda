{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfMultiplierRound805Exact where

------------------------------------------------------------------------
-- ROUND805 / LIFT R720'S ZERO-SAFE MULTIPLIER CARRIER THROUGH THE SEP MASK
--
-- R804 isolates the zero-safe separated selected-self cell:
--
--   Self0_sep(tau) = chi_sep(tau) * R714.Self0(tau).
--
-- R720 already proves on the SAME R714 cell:
--
--   MultSelf(tau) = Self0(tau) + Self0(tau).
--
-- Since the separated mask is only an outer 0/1 selector, masking this
-- pointwise theorem gives exactly
--
--   MultSelf_sep(tau)
--     = Self0_sep(tau) + Self0_sep(tau).
--
-- Hence, output by output and after coherent work,
--
--   W(M_k,MultSelf_sep,k)
--     = 2 W(M_k,Self0_sep,k).
--
-- Globally:
--
--   MultWork_sep = 2 * ZeroSafeSelfWork_sep.
--
-- This moves the complete zero-safe self branch onto R625's literal
-- four-helicity multiplier-difference carrier with no division or estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650SelectedSelfMultiplierFoldRound720Exact as R720
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfZeroSafeSplitRound804Exact as R804

two : ℚ
two = 2

module SeparatedSelfMultiplier
    (physicalSystem :
      Field30.PhysicalFiniteComplex3GalerkinSystem R804.R803.R802.F)
    (S : Helical.HelicalModeScalars R804.R803.R802.F)
    (L : Helical.PeriodicHelicalProjectorLaws R804.R803.R802.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (velocityReality :
      Reality.RealityCondition
        (Audit.velocity (Field30.finiteSystem physicalSystem))) where

  module Sep =
    R804.SeparatedSelfZeroSafe
      physicalSystem S L H velocityTransverse

  module Mult =
    R720.SelectedSelfMultiplierFold
      physicalSystem S L H velocityTransverse velocityReality

  cutoff = Sep.cutoff

  maskedMultiplierCell :
    Physical.PhysicalTriadIncidence →
    C3.Complex3 R804.R803.R802.F
  maskedMultiplierCell beta with R781.ccTouched beta
  ... | true = C3.complex3Zero R804.R803.R802.F
  ... | false = Mult.multiplierCell beta

  zeroSafeSameR720 :
    (beta : Physical.PhysicalTriadIncidence) →
    Sep.Single.singleSelfCommutator beta ≡ Mult.Out.selfCell beta
  zeroSafeSameR720 beta = refl

  maskedMultiplierIsDoubleZeroSafe :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedMultiplierCell beta
    ≡
    C3.complex3Add
      (Sep.maskedZeroSafeSelf beta)
      (Sep.maskedZeroSafeSelf beta)
  maskedMultiplierIsDoubleZeroSafe beta
    with R781.ccTouched beta
  ... | true =
    sym (Field.complex3AddZeroLeft
      (C3.complex3Zero R804.R803.R802.F))
  ... | false =
    trans
      (Mult.multiplierCellIsDoubleSelfCell beta)
      (cong₂ C3.complex3Add
        (sym (zeroSafeSameR720 beta))
        (sym (zeroSafeSameR720 beta)))

  multiplierFold : Z3.FourierMode →
    C3.Complex3 R804.R803.R802.F
  multiplierFold output =
    R224.foldVector maskedMultiplierCell
      (Output.physicalOutputFiber cutoff output)

  multiplierFoldIsDoubleZeroSafe :
    (output : Z3.FourierMode) →
    multiplierFold output
    ≡
    C3.complex3Add
      (Sep.zeroSafeFold output)
      (Sep.zeroSafeFold output)
  multiplierFoldIsDoubleZeroSafe output =
    let
      items = Output.physicalOutputFiber cutoff output
    in
    trans
      (Mult.foldPointwiseEqual
        maskedMultiplierCell
        (λ beta →
          C3.complex3Add
            (Sep.maskedZeroSafeSelf beta)
            (Sep.maskedZeroSafeSelf beta))
        maskedMultiplierIsDoubleZeroSafe
        items)
      (R230.foldAdd
        Sep.maskedZeroSafeSelf
        Sep.maskedZeroSafeSelf
        items)

  outputMultiplierWork : Z3.FourierMode → ℚ
  outputMultiplierWork output =
    Work.coherentWork
      (Sep.Sep.Split.Id.mixedFold output)
      (multiplierFold output)

  selectedMultiplierWork : Z3.FourierMode → ℚ
  selectedMultiplierWork output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = outputMultiplierWork output

  selectedMultiplierWorkIsDoubleZeroSafe :
    (output : Z3.FourierMode) →
    selectedMultiplierWork output
    ≡
    Sep.selectedZeroSafeWork output
      + Sep.selectedZeroSafeWork output
  selectedMultiplierWorkIsDoubleZeroSafe output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    trans
      (cong
        (Work.coherentWork (Sep.Sep.Split.Id.mixedFold output))
        (multiplierFoldIsDoubleZeroSafe output))
      (Work.workAddRight
        (Sep.Sep.Split.Id.mixedFold output)
        (Sep.zeroSafeFold output)
        (Sep.zeroSafeFold output))

  sumMultiplierWork : List Z3.FourierMode → ℚ
  sumMultiplierWork [] = 0ℚ
  sumMultiplierWork (output ∷ rest) =
    selectedMultiplierWork output + sumMultiplierWork rest

  globalMultiplierWork : ℚ
  globalMultiplierWork =
    sumMultiplierWork (Cube.cutoffModes cutoff)

  globalMultiplierWorkIsDoubleZeroSafe :
    globalMultiplierWork
    ≡ two * Sep.globalZeroSafeSelfWork
  globalMultiplierWorkIsDoubleZeroSafe =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      sumMultiplierWork outputs
      ≡ two * Sep.sumZeroSafeWork outputs
    go [] = solve (two ∷ [])
    go (output ∷ rest) =
      trans
        (cong₂ _+_
          (selectedMultiplierWorkIsDoubleZeroSafe output)
          (go rest))
        (solve
          ( two
          ∷ Sep.selectedZeroSafeWork output
          ∷ Sep.sumZeroSafeWork rest
          ∷ []))

round805SeparatedZeroSafeSelfMovedToMultiplierCarrier : Bool
round805SeparatedZeroSafeSelfMovedToMultiplierCarrier = true

round805MultiplierWorkIsDoubleZeroSafeSelfWork : Bool
round805MultiplierWorkIsDoubleZeroSafeSelfWork = true

round805IntroducesEstimate : Bool
round805IntroducesEstimate = false

round805PZeroDefectClosed : Bool
round805PZeroDefectClosed = false

round805ExternalDefectClosed : Bool
round805ExternalDefectClosed = false

round805W2Closed : Bool
round805W2Closed = false

round805ClayPromotion : Bool
round805ClayPromotion = false

round805SeparatedZeroSafeSelfMovedToMultiplierCarrierIsTrue :
  round805SeparatedZeroSafeSelfMovedToMultiplierCarrier ≡ true
round805SeparatedZeroSafeSelfMovedToMultiplierCarrierIsTrue = refl

round805MultiplierWorkIsDoubleZeroSafeSelfWorkIsTrue :
  round805MultiplierWorkIsDoubleZeroSafeSelfWork ≡ true
round805MultiplierWorkIsDoubleZeroSafeSelfWorkIsTrue = refl

round805IntroducesEstimateIsFalse :
  round805IntroducesEstimate ≡ false
round805IntroducesEstimateIsFalse = refl

round805W2ClosedIsFalse :
  round805W2Closed ≡ false
round805W2ClosedIsFalse = refl

round805ClayPromotionIsFalse :
  round805ClayPromotion ≡ false
round805ClayPromotionIsFalse = refl
