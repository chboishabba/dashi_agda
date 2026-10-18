{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceFoldRound626Exact where

------------------------------------------------------------------------
-- ROUND626 / FIXED-OUTPUT R573 SELF FOLD ON FOUR MULTIPLIER-DIFFERENCE CELLS
--
-- R625 rewrites every R613 self nested cell, preserving the p=0 zero branch,
-- onto the doubled four-helicity multiplier-difference normal form.
--
-- This owner lifts that pointwise equality through the complete physical
-- fixed-output fibre.  It introduces no estimate, norm, absolute value,
-- reindexing, or additional hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceExpansionRound625Exact as R625

module SelfMultiplierFold
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Split =
    R613.NestedNetworkSplit W S L H system velocityTransverse
  module Mult =
    R625.SelfMultiplierExpansion W S L H system velocityTransverse

  foldPointwiseEqual :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldPointwiseEqual left right pointwise [] = refl
  foldPointwiseEqual left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldPointwiseEqual left right pointwise rest)

  selfMultiplierNestedFold :
    Z3.FourierMode → C3.Complex3 F
  selfMultiplierNestedFold output =
    R224.foldVector Mult.selfNestedMultiplierCompanion
      (Output.physicalOutputFiber (Audit.cutoff system) output)

  fixedOutputSelfNestedFoldIsMultiplierDifference :
    (output : Z3.FourierMode) →
    R224.foldVector Split.selfNestedWeightedCompanionCell
      (Output.physicalOutputFiber (Audit.cutoff system) output)
    ≡ selfMultiplierNestedFold output
  fixedOutputSelfNestedFoldIsMultiplierDifference output =
    foldPointwiseEqual
      Split.selfNestedWeightedCompanionCell
      Mult.selfNestedMultiplierCompanion
      Mult.selfNestedCompanionMultiplierNormalForm
      (Output.physicalOutputFiber (Audit.cutoff system) output)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round626FixedOutputSelfR573MultiplierDifferenceFoldClosed : Bool
round626FixedOutputSelfR573MultiplierDifferenceFoldClosed = true

round626PreservesZeroPBranch : Bool
round626PreservesZeroPBranch = true

round626IntroducesEstimate : Bool
round626IntroducesEstimate = false

round626SelfSignedPaymentClosed : Bool
round626SelfSignedPaymentClosed = false

round626FixedOutputSelfR573MultiplierDifferenceFoldClosedIsTrue :
  round626FixedOutputSelfR573MultiplierDifferenceFoldClosed ≡ true
round626FixedOutputSelfR573MultiplierDifferenceFoldClosedIsTrue = refl

round626IntroducesEstimateIsFalse :
  round626IntroducesEstimate ≡ false
round626IntroducesEstimateIsFalse = refl

round626SelfSignedPaymentClosedIsFalse :
  round626SelfSignedPaymentClosed ≡ false
round626SelfSignedPaymentClosedIsFalse = refl
