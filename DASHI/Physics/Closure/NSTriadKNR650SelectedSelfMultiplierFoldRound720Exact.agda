{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelectedSelfMultiplierFoldRound720Exact where

------------------------------------------------------------------------
-- ROUND720 / R714 ONE-COPY SELF FOLD -> R625 MULTIPLIER-DIFFERENCE FOLD
--
-- R719 leaves the exact fixed-output scalar
--
--   W(M_k,C_k^self).
--
-- The repository already owns a sharper vector normal form.  R625 rewrites the
-- unit-weight R613 selected-self slot as the sum of four literal helical
-- multiplier-difference slots, while R711 identifies that SAME slot as two
-- copies of the selected-self R230 commutator.
--
-- Preserving R714's literal p=0 branch therefore gives cellwise
--
--   MultSelf*(tau) = C_self*(tau) + C_self*(tau),
--
-- and after the complete fixed-output fibre fold,
--
--   MultSelf_k = C_k^self + C_k^self.
--
-- Consequently
--
--   W(M_k,MultSelf_k) = 2 W(M_k,C_k^self).
--
-- This avoids division and moves the entire remaining self question onto the
-- mature R571/R625 four-helicity multiplier-difference carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR573SelfMultiplierDifferenceExpansionRound625Exact as R625
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SelfWeightedSlotCommutatorRound711Exact as R711
import DASHI.Physics.Closure.NSTriadKNR650SelectedSelfFoldRealityRound719Exact as R719

module SelectedSelfMultiplierFold
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
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

  module Prev =
    R719.SelectedSelfReality
      physicalSystem S L H velocityTransverse velocityReality
  module Out = Prev.Out
  module One = Out.One

  system = Field30.finiteSystem physicalSystem

  module Mult =
    R625.SelfMultiplierExpansion
      R694.unitWeight S L H system velocityTransverse

  module Slot =
    R711.SelfSlotCommutator
      R694.unitWeight S L H system velocityTransverse

  multiplierCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  multiplierCell = Mult.selfMultiplierExhaustiveCompanion

  multiplierFold :
    Z3.FourierMode → C3.Complex3 R694.F
  multiplierFold output =
    R224.foldVector multiplierCell (Out.fibre output)

  multiplierCellIsDoubleSelfCell :
    (tau : Physical.PhysicalTriadIncidence) →
    multiplierCell tau
    ≡ C3.complex3Add (Out.selfCell tau) (Out.selfCell tau)
  multiplierCellIsDoubleSelfCell tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true =
    sym R613.zeroPlusZero
  ... | false =
    let
      pNonzero = One.Carrier.Normal.pNonzeroFromDecision tau pDecision
      C = Slot.Self.selfCommutatorCell tau
    in
    trans
      (sym (Mult.selfExhaustiveCompanionMultiplierNormalForm tau))
      (trans
        (Slot.weightedSelfSlotIsWeightedDoubleSelfCell tau pNonzero)
        (R106.complex3ScaleOne (C3.complex3Add C C)))

  foldPointwiseEqual :
    (left right :
      Physical.PhysicalTriadIncidence → C3.Complex3 R694.F) →
    ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector left items ≡ R224.foldVector right items
  foldPointwiseEqual left right pointwise [] = refl
  foldPointwiseEqual left right pointwise (tau ∷ rest) =
    cong₂ C3.complex3Add
      (pointwise tau)
      (foldPointwiseEqual left right pointwise rest)

  multiplierFoldIsDoubleSelfFold :
    (output : Z3.FourierMode) →
    multiplierFold output
    ≡ C3.complex3Add (Out.selfFold output) (Out.selfFold output)
  multiplierFoldIsDoubleSelfFold output =
    trans
      (foldPointwiseEqual
        multiplierCell
        (λ tau → C3.complex3Add (Out.selfCell tau) (Out.selfCell tau))
        multiplierCellIsDoubleSelfCell
        (Out.fibre output))
      (R230.foldAdd Out.selfCell Out.selfCell (Out.fibre output))

  multiplierWorkIsDoubleSelfWork :
    (output : Z3.FourierMode) →
    Work.coherentWork (Out.mixedFold output) (multiplierFold output)
    ≡
    Work.coherentWork (Out.mixedFold output) (Out.selfFold output)
      + Work.coherentWork (Out.mixedFold output) (Out.selfFold output)
  multiplierWorkIsDoubleSelfWork output =
    trans
      (cong₂ Work.coherentWork refl (multiplierFoldIsDoubleSelfFold output))
      (Work.workAddRight
        (Out.mixedFold output)
        (Out.selfFold output)
        (Out.selfFold output))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round720ZeroSafeMultiplierCellIsDoubleSelectedSelfCell : Bool
round720ZeroSafeMultiplierCellIsDoubleSelectedSelfCell = true

round720FixedOutputMultiplierFoldIsDoubleSelectedSelfFold : Bool
round720FixedOutputMultiplierFoldIsDoubleSelectedSelfFold = true

round720MultiplierWorkIsDoubleSelectedSelfWork : Bool
round720MultiplierWorkIsDoubleSelectedSelfWork = true

round720RemainingSelfQuestionMovedToR625MultiplierCarrier : Bool
round720RemainingSelfQuestionMovedToR625MultiplierCarrier = true

round720IntroducesEstimate : Bool
round720IntroducesEstimate = false

round720SelectedSelfCancellationClosed : Bool
round720SelectedSelfCancellationClosed = false

round720ClayPromotion : Bool
round720ClayPromotion = false

round720ZeroSafeMultiplierCellIsDoubleSelectedSelfCellIsTrue :
  round720ZeroSafeMultiplierCellIsDoubleSelectedSelfCell ≡ true
round720ZeroSafeMultiplierCellIsDoubleSelectedSelfCellIsTrue = refl

round720FixedOutputMultiplierFoldIsDoubleSelectedSelfFoldIsTrue :
  round720FixedOutputMultiplierFoldIsDoubleSelectedSelfFold ≡ true
round720FixedOutputMultiplierFoldIsDoubleSelectedSelfFoldIsTrue = refl

round720MultiplierWorkIsDoubleSelectedSelfWorkIsTrue :
  round720MultiplierWorkIsDoubleSelectedSelfWork ≡ true
round720MultiplierWorkIsDoubleSelectedSelfWorkIsTrue = refl

round720RemainingSelfQuestionMovedToR625MultiplierCarrierIsTrue :
  round720RemainingSelfQuestionMovedToR625MultiplierCarrier ≡ true
round720RemainingSelfQuestionMovedToR625MultiplierCarrierIsTrue = refl

round720IntroducesEstimateIsFalse :
  round720IntroducesEstimate ≡ false
round720IntroducesEstimateIsFalse = refl

round720SelectedSelfCancellationClosedIsFalse :
  round720SelectedSelfCancellationClosed ≡ false
round720SelectedSelfCancellationClosedIsFalse = refl

round720ClayPromotionIsFalse :
  round720ClayPromotion ≡ false
round720ClayPromotionIsFalse = refl
