module DASHI.Analysis.RiemannG2SelectedDirectCutoffFinalOffSameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Weld
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2PoleQuotientOffIntermediateAllowanceCompilerExact as Intermediate
import DASHI.Analysis.RiemannG2FinalSplitComplementSameObjectAssemblyExact as Cast

------------------------------------------------------------------------
-- SELECTED/DIRECT CUTOFF -> FINAL OFF CUTOFF, SAME OBJECT
--
-- ActualSelectedPoleNearProducer intentionally does not duplicate a scalar cutoff
-- coordinate: its window only carries the proof-bearing nearOffFinset preservation
-- receipt. DirectFinitePoleNearProducer already owns a typed cutoff, and the
-- SelectedDirectFiniteWeld already owns the claim that this is the selected
-- cutoff. Reuse that coordinate rather than inventing a second selected J.
------------------------------------------------------------------------

record SelectedDirectFinalOffCutoffBridge
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    (direct : Direct.DirectFinitePoleNearProducer)
    (weld : Weld.SelectedDirectFiniteWeld space formula orbit selected direct)
    (S : NearFar.OrderedAdditiveNearFarSurface)
    (input : Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput S)
    : Set₁ where
  field
    directScalarIsFinalCutoffCarrier :
      Direct.DirectFinitePoleNearProducer.Scalar direct
      ≡ Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.Cutoff input

    directCutoffIsFinalChosenCutoff :
      Cast.cast directScalarIsFinalCutoffCarrier
        (Direct.DirectFinitePoleNearProducer.cutoff direct)
      ≡ Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoff input

    selectedDirectCutoffReceipt :
      Weld.SelectedDirectFiniteWeld.sameSelectedCutoff weld

    finalChosenCutoffCrosses :
      Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.CrossingCutoff input
        (Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoff input)

    cutoffBridgeReference : String

open SelectedDirectFinalOffCutoffBridge public

------------------------------------------------------------------------
-- The final crossing receipt is reused directly. The bridge does not select a
-- new J and does not infer a crossing from the selected-window preservation Set.
------------------------------------------------------------------------

compiledFinalChosenCutoffCrossing :
  ∀ {space formula orbit selected direct weld S input} →
  SelectedDirectFinalOffCutoffBridge
    space formula orbit selected direct weld S input →
  Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.CrossingCutoff input
    (Intermediate.DirectPoleQuotientOffIntermediateAllowanceInput.chosenCutoff input)
compiledFinalChosenCutoffCrossing bridge = finalChosenCutoffCrosses bridge

record SelectedDirectFinalOffCutoffBoundary : Set where
  constructor selected-direct-final-off-cutoff-boundary
  field
    secondSelectedCutoffCoordinateRequired : Bool
    secondSelectedCutoffCoordinateRequiredIsFalse :
      secondSelectedCutoffCoordinateRequired ≡ false

    directProducerAlreadyOwnsTypedCutoff : Bool
    directProducerAlreadyOwnsTypedCutoffIsTrue :
      directProducerAlreadyOwnsTypedCutoff ≡ true

    selectedDirectWeldAlreadyOwnsSameCutoffReceipt : Bool
    selectedDirectWeldAlreadyOwnsSameCutoffReceiptIsTrue :
      selectedDirectWeldAlreadyOwnsSameCutoffReceipt ≡ true

    finalCutoffIdentityStillNeedsTypedTransport : Bool
    finalCutoffIdentityStillNeedsTypedTransportIsTrue :
      finalCutoffIdentityStillNeedsTypedTransport ≡ true

    farTailMayChooseDifferentIndependentFinalCutoff : Bool
    farTailMayChooseDifferentIndependentFinalCutoffIsFalse :
      farTailMayChooseDifferentIndependentFinalCutoff ≡ false

    cutoffBridgeCreatesNewAnalyticEstimate : Bool
    cutoffBridgeCreatesNewAnalyticEstimateIsFalse :
      cutoffBridgeCreatesNewAnalyticEstimate ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedDirectFinalOffCutoffBoundary :
  SelectedDirectFinalOffCutoffBoundary
canonicalSelectedDirectFinalOffCutoffBoundary =
  selected-direct-final-off-cutoff-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Do not add a second selected-window cutoff field. DirectFinitePoleNearProducer already has a typed cutoff, and SelectedDirectFiniteWeld already carries a proof-bearing same-selected-cutoff receipt. Identify the direct scalar/cutoff carrier with the final Off Cutoff type and prove that the direct cutoff casts to the final chosen crossing cutoff. This is same-object representation work, not a new zero estimate. Far-tail decay still cannot choose a different final J independently, and RH remains open."
