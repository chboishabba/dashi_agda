module DASHI.Physics.Closure.NSConditionalQGronwallTheoremGReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed receipt for the conditional Q-Gronwall Theorem G surface.
--
-- This module records the theorem surface only.  It keeps the h_delta1
-- threshold explicit, records the mu = 2 * delta1 - 1 / delta1 positivity
-- claim as a conditional row, carries the F123 damping term and the
-- Rellich-Kato commutator bound as checked receipt data, and names the
-- moving-boundary and viscous H5 terms explicitly.  The Gronwall
-- conclusion is recorded only as a conditional conclusion under h_delta1,
-- while collapseImpossible, hDelta1Promoted, kornLevelSetPromoted, and
-- clayNavierStokesPromoted are all left false.
--
-- It also now records two separate contradiction requirements:
--   (i) finite-time blow-up implies Q2/carrier divergence,
--  (ii) TheoremG + GD1 gives a conditional uniform Q2 bound.
-- Neither implication is discharged by this receipt.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSConditionalQGronwallTheoremGStatus : Set where
  checkedConditionalQGronwallTheoremGReceiptRecorded :
    NSConditionalQGronwallTheoremGStatus

data NSConditionalQGronwallTheoremGStage : Set where
  theoremSurfaceRecorded :
    NSConditionalQGronwallTheoremGStage
  hDelta1HypothesisRecorded :
    NSConditionalQGronwallTheoremGStage
  delta1ThresholdRecorded :
    NSConditionalQGronwallTheoremGStage
  muPositivityRecorded :
    NSConditionalQGronwallTheoremGStage
  f123ExactDampingRecorded :
    NSConditionalQGronwallTheoremGStage
  rellichKatoCommutatorRecorded :
    NSConditionalQGronwallTheoremGStage
  gd1NoCollapseRecorded :
    NSConditionalQGronwallTheoremGStage
  layerCZLayerKornRecorded :
    NSConditionalQGronwallTheoremGStage
  viscousLowerOrderH5Recorded :
    NSConditionalQGronwallTheoremGStage
  movingBoundarySmoothBeforeTStarRecorded :
    NSConditionalQGronwallTheoremGStage
  qFiniteConclusionRecorded :
    NSConditionalQGronwallTheoremGStage
  q2ContradictionChannelRecorded :
    NSConditionalQGronwallTheoremGStage
  q2BlowupToCarrierDivergenceRecorded :
    NSConditionalQGronwallTheoremGStage
  theoremGPlusGD1UniformQ2BoundRecorded :
    NSConditionalQGronwallTheoremGStage
  contradictionRouteVisibleRecorded :
    NSConditionalQGronwallTheoremGStage
  failClosedPromotionsFalseRecorded :
    NSConditionalQGronwallTheoremGStage

canonicalNSConditionalQGronwallTheoremGStages :
  List NSConditionalQGronwallTheoremGStage
canonicalNSConditionalQGronwallTheoremGStages =
  theoremSurfaceRecorded
  ∷ hDelta1HypothesisRecorded
  ∷ delta1ThresholdRecorded
  ∷ muPositivityRecorded
  ∷ f123ExactDampingRecorded
  ∷ rellichKatoCommutatorRecorded
  ∷ gd1NoCollapseRecorded
  ∷ layerCZLayerKornRecorded
  ∷ viscousLowerOrderH5Recorded
  ∷ movingBoundarySmoothBeforeTStarRecorded
  ∷ qFiniteConclusionRecorded
  ∷ q2ContradictionChannelRecorded
  ∷ q2BlowupToCarrierDivergenceRecorded
  ∷ theoremGPlusGD1UniformQ2BoundRecorded
  ∷ contradictionRouteVisibleRecorded
  ∷ failClosedPromotionsFalseRecorded
  ∷ []

data NSConditionalQGronwallTheoremGBlocker : Set where
  hDelta1StillHypothesis :
    NSConditionalQGronwallTheoremGBlocker
  delta1ThresholdStillConditional :
    NSConditionalQGronwallTheoremGBlocker
  muPositivityStillRecordedNotPromoted :
    NSConditionalQGronwallTheoremGBlocker
  f123DampingExactnessStillDiagnostic :
    NSConditionalQGronwallTheoremGBlocker
  rellichKatoCommutatorBoundStillOpen :
    NSConditionalQGronwallTheoremGBlocker
  viscousLowerOrderH5ControlStillOpen :
    NSConditionalQGronwallTheoremGBlocker
  movingBoundarySmoothnessStillHypothesis :
    NSConditionalQGronwallTheoremGBlocker
  qFiniteConclusionStillConditional :
    NSConditionalQGronwallTheoremGBlocker
  q2BlowupImplicationNotDischarged :
    NSConditionalQGronwallTheoremGBlocker
  q2UniformBoundImplicationNotDischarged :
    NSConditionalQGronwallTheoremGBlocker
  hDelta1NotDischarged :
    NSConditionalQGronwallTheoremGBlocker
  hDelta1PromotionBlocked :
    NSConditionalQGronwallTheoremGBlocker
  kornLevelSetPromotionBlocked :
    NSConditionalQGronwallTheoremGBlocker
  collapseImpossiblePromotionBlocked :
    NSConditionalQGronwallTheoremGBlocker
  clayNavierStokesPromotionBlocked :
    NSConditionalQGronwallTheoremGBlocker

canonicalNSConditionalQGronwallTheoremGBlockers :
  List NSConditionalQGronwallTheoremGBlocker
canonicalNSConditionalQGronwallTheoremGBlockers =
  hDelta1StillHypothesis
  ∷ delta1ThresholdStillConditional
  ∷ muPositivityStillRecordedNotPromoted
  ∷ f123DampingExactnessStillDiagnostic
  ∷ rellichKatoCommutatorBoundStillOpen
  ∷ viscousLowerOrderH5ControlStillOpen
  ∷ movingBoundarySmoothnessStillHypothesis
  ∷ qFiniteConclusionStillConditional
  ∷ q2BlowupImplicationNotDischarged
  ∷ q2UniformBoundImplicationNotDischarged
  ∷ hDelta1NotDischarged
  ∷ hDelta1PromotionBlocked
  ∷ kornLevelSetPromotionBlocked
  ∷ collapseImpossiblePromotionBlocked
  ∷ clayNavierStokesPromotionBlocked
  ∷ []

canonicalNSConditionalQGronwallTheoremGDependencyNames : List String
canonicalNSConditionalQGronwallTheoremGDependencyNames =
  "TheoremG conditional Q2/time-integral channel surface"
  ∷ "h_delta1 hypothesis (input-only threshold)"
  ∷ "GD1 no-collapse route on the biaxial carrier"
  ∷ "Rellich-Kato commutator bound <= (1 / delta1) * Q"
  ∷ "LayerCZ hypothesis for commutator decomposition"
  ∷ "LayerKorn coercive control hypothesis"
  ∷ "moving-boundary smooth-before-T* transport regularity"
  ∷ "viscous H5 control term"
  ∷ "finite-time blow-up => Q2/carrier divergence implication"
  ∷ "TheoremG + GD1 => uniform Q2 bound implication"
  ∷ []

theoremSurfaceTextValue : String
theoremSurfaceTextValue =
  "conditionalQGronwallTheoremGRecorded: the conditional Q-Gronwall Theorem G surface is recorded as a fail-closed receipt, with h_delta1 explicit, mu positivity conditional, the F123 damping term tracked, the Rellich-Kato commutator bound tracked, the viscous H5 term tracked, the moving-boundary smooth-before-T* term tracked, and the Q(t) finiteness conclusion kept conditional."

hDelta1HypothesisTextValue : String
hDelta1HypothesisTextValue =
  "h_delta1 hypothesis: delta1 > 1 / sqrt(2) is recorded as the input threshold and not promoted to an unconditional theorem."

delta1ThresholdTextValue : String
delta1ThresholdTextValue =
  "Threshold row: delta1 is kept above the 1 / sqrt(2)-style barrier only as a checked hypothesis surface."

muPositivityTextValue : String
muPositivityTextValue =
  "mu = 2 * delta1 - 1 / delta1 is recorded as positive once the h_delta1 threshold is supplied."

f123ExactDampingTextValue : String
f123ExactDampingTextValue =
  "F123 exact damping term: the damping factor is recorded exactly rather than approximated or absorbed."

rellichKatoCommutatorTextValue : String
rellichKatoCommutatorTextValue =
  "Rellich-Kato commutator row: the commutator is recorded with the bound <= (1 / delta1) * Q."

viscousLowerOrderH5TextValue : String
viscousLowerOrderH5TextValue =
  "Viscous lower-order H5 term: the H5 contribution is recorded as a lower-order viscous term in the ledger."

movingBoundarySmoothBeforeTStarTextValue : String
movingBoundarySmoothBeforeTStarTextValue =
  "Moving-boundary term: smooth-before-T* regularity is recorded explicitly for the boundary transport term."

qFiniteConclusionTextValue : String
qFiniteConclusionTextValue =
  "Conclusion row: Q(t) is finite under h_delta1, but only as the conditional conclusion surface recorded here."

q2ContradictionRouteTextValue : String
q2ContradictionRouteTextValue =
  "TheoremG supplies a conditional Q2/time-integral route under h_delta1 + GD1 no-collapse + RK commutator + LayerCZ/LayerKorn + smooth boundary + H5."

q2BlowupImplicationTextValue : String
q2BlowupImplicationTextValue =
  "Implication requirement 1: finite-time blow-up forces Q2 or carrier divergence."

q2UniformBoundImplicationTextValue : String
q2UniformBoundImplicationTextValue =
  "Implication requirement 2: TheoremG + GD1 gives a conditional uniform Q2 bound."

receiptBoundaryText : List String
receiptBoundaryText =
  "conditionalQGronwallTheoremGRecorded is the theorem surface"
  ∷ "h_delta1 is recorded as a threshold hypothesis"
  ∷ "delta1 > 1 / sqrt(2) is tracked as the threshold row"
  ∷ "mu = 2 * delta1 - 1 / delta1 is recorded as positive under the threshold"
  ∷ "F123 is recorded as an exact damping term"
  ∷ "Rellich-Kato commutator <= (1 / delta1) * Q is recorded"
  ∷ "viscous lower-order H5 is recorded explicitly"
  ∷ "moving-boundary smooth-before-T* regularity is recorded explicitly"
  ∷ "Q(t) finite is recorded only conditionally under h_delta1"
  ∷ "TheoremG conditional Q2/time-integral contradiction route is recorded as visible"
  ∷ "finite-time blow-up -> Q2/carrier divergence implication is required and not discharged"
  ∷ "TheoremG + GD1 -> uniform Q2 bound implication is required and not discharged"
  ∷ "collapseImpossible remains false"
  ∷ "hDelta1Promoted remains false"
  ∷ "kornLevelSetPromoted remains false"
  ∷ "clayNavierStokesPromoted remains false"
  ∷ []

record NSConditionalQGronwallTheoremGReceipt : Setω where
  field
    status :
      NSConditionalQGronwallTheoremGStatus
    statusIsCanonical :
      status ≡ checkedConditionalQGronwallTheoremGReceiptRecorded

    stageTrail :
      List NSConditionalQGronwallTheoremGStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSConditionalQGronwallTheoremGStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSConditionalQGronwallTheoremGStages

    blockerTrail :
      List NSConditionalQGronwallTheoremGBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSConditionalQGronwallTheoremGBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSConditionalQGronwallTheoremGBlockers

    conditionalQGronwallTheoremGRecorded :
      String
    conditionalQGronwallTheoremGRecordedIsCanonical :
      conditionalQGronwallTheoremGRecorded ≡ theoremSurfaceTextValue

    hDelta1HypothesisText :
      String
    hDelta1HypothesisTextIsCanonical :
      hDelta1HypothesisText ≡ hDelta1HypothesisTextValue

    delta1ThresholdText :
      String
    delta1ThresholdTextIsCanonical :
      delta1ThresholdText ≡ delta1ThresholdTextValue

    muPositivityText :
      String
    muPositivityTextIsCanonical :
      muPositivityText ≡ muPositivityTextValue

    f123ExactDampingTermText :
      String
    f123ExactDampingTermTextIsCanonical :
      f123ExactDampingTermText ≡ f123ExactDampingTextValue

    rellichKatoCommutatorText :
      String
    rellichKatoCommutatorTextIsCanonical :
      rellichKatoCommutatorText ≡ rellichKatoCommutatorTextValue

    viscousLowerOrderH5TermText :
      String
    viscousLowerOrderH5TermTextIsCanonical :
      viscousLowerOrderH5TermText ≡ viscousLowerOrderH5TextValue

    movingBoundarySmoothBeforeTStarText :
      String
    movingBoundarySmoothBeforeTStarTextIsCanonical :
      movingBoundarySmoothBeforeTStarText ≡ movingBoundarySmoothBeforeTStarTextValue

    qFiniteConclusionText :
      String
    qFiniteConclusionTextIsCanonical :
      qFiniteConclusionText ≡ qFiniteConclusionTextValue
    q2ContradictionRouteText :
      String
    q2ContradictionRouteTextIsCanonical :
      q2ContradictionRouteText ≡ q2ContradictionRouteTextValue
    q2BlowupImplicationText :
      String
    q2BlowupImplicationTextIsCanonical :
      q2BlowupImplicationText ≡ q2BlowupImplicationTextValue
    q2UniformBoundImplicationText :
      String
    q2UniformBoundImplicationTextIsCanonical :
      q2UniformBoundImplicationText ≡ q2UniformBoundImplicationTextValue

    dependencyNames :
      List String
    dependencyNamesIsCanonical :
      dependencyNames ≡ canonicalNSConditionalQGronwallTheoremGDependencyNames
    dependencyNameCount :
      Nat
    dependencyNameCountIsCanonical :
      dependencyNameCount ≡
      listLength canonicalNSConditionalQGronwallTheoremGDependencyNames

    hDelta1Hypothesis :
      Bool
    hDelta1HypothesisIsTrue :
      hDelta1Hypothesis ≡ true

    muPositive :
      Bool
    muPositiveIsTrue :
      muPositive ≡ true

    movingBoundarySmoothBeforeTStar :
      Bool
    movingBoundarySmoothBeforeTStarIsTrue :
      movingBoundarySmoothBeforeTStar ≡ true

    q2ContradictionRouteVisible :
      Bool
    q2ContradictionRouteVisibleIsTrue :
      q2ContradictionRouteVisible ≡ true

    q2BlowupImplicationDischarged :
      Bool
    q2BlowupImplicationDischargedIsFalse :
      q2BlowupImplicationDischarged ≡ false

    q2UniformBoundDischarged :
      Bool
    q2UniformBoundDischargedIsFalse :
      q2UniformBoundDischarged ≡ false

    hDelta1Discharged :
      Bool
    hDelta1DischargedIsFalse :
      hDelta1Discharged ≡ false

    hDelta1Promoted :
      Bool
    hDelta1PromotedIsFalse :
      hDelta1Promoted ≡ false

    collapseImpossible :
      Bool
    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    kornLevelSetPromoted :
      Bool
    kornLevelSetPromotedIsFalse :
      kornLevelSetPromoted ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText

data NSConditionalQGronwallTheoremGPromotion : Set where

nsConditionalQGronwallTheoremGPromotionImpossibleHere :
  NSConditionalQGronwallTheoremGPromotion → ⊥
nsConditionalQGronwallTheoremGPromotionImpossibleHere ()

canonicalNSConditionalQGronwallTheoremGReceipt :
  NSConditionalQGronwallTheoremGReceipt
canonicalNSConditionalQGronwallTheoremGReceipt =
  record
    { status =
        checkedConditionalQGronwallTheoremGReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageTrail =
        canonicalNSConditionalQGronwallTheoremGStages
    ; stageTrailIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSConditionalQGronwallTheoremGStages
    ; stageCountIsCanonical =
        refl
    ; blockerTrail =
        canonicalNSConditionalQGronwallTheoremGBlockers
    ; blockerTrailIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSConditionalQGronwallTheoremGBlockers
    ; blockerCountIsCanonical =
        refl
    ; conditionalQGronwallTheoremGRecorded =
        theoremSurfaceTextValue
    ; conditionalQGronwallTheoremGRecordedIsCanonical =
        refl
    ; hDelta1HypothesisText =
        hDelta1HypothesisTextValue
    ; hDelta1HypothesisTextIsCanonical =
        refl
    ; delta1ThresholdText =
        delta1ThresholdTextValue
    ; delta1ThresholdTextIsCanonical =
        refl
    ; muPositivityText =
        muPositivityTextValue
    ; muPositivityTextIsCanonical =
        refl
    ; f123ExactDampingTermText =
        f123ExactDampingTextValue
    ; f123ExactDampingTermTextIsCanonical =
        refl
    ; rellichKatoCommutatorText =
        rellichKatoCommutatorTextValue
    ; rellichKatoCommutatorTextIsCanonical =
        refl
    ; viscousLowerOrderH5TermText =
        viscousLowerOrderH5TextValue
    ; viscousLowerOrderH5TermTextIsCanonical =
        refl
    ; movingBoundarySmoothBeforeTStarText =
        movingBoundarySmoothBeforeTStarTextValue
    ; movingBoundarySmoothBeforeTStarTextIsCanonical =
        refl
    ; qFiniteConclusionText =
        qFiniteConclusionTextValue
    ; qFiniteConclusionTextIsCanonical =
        refl
    ; q2ContradictionRouteText =
        q2ContradictionRouteTextValue
    ; q2ContradictionRouteTextIsCanonical =
        refl
    ; q2BlowupImplicationText =
        q2BlowupImplicationTextValue
    ; q2BlowupImplicationTextIsCanonical =
        refl
    ; q2UniformBoundImplicationText =
        q2UniformBoundImplicationTextValue
    ; q2UniformBoundImplicationTextIsCanonical =
        refl
    ; dependencyNames =
        canonicalNSConditionalQGronwallTheoremGDependencyNames
    ; dependencyNamesIsCanonical =
        refl
    ; dependencyNameCount =
        listLength canonicalNSConditionalQGronwallTheoremGDependencyNames
    ; dependencyNameCountIsCanonical =
        refl
    ; hDelta1Hypothesis =
        true
    ; hDelta1HypothesisIsTrue =
        refl
    ; muPositive =
        true
    ; muPositiveIsTrue =
        refl
    ; movingBoundarySmoothBeforeTStar =
        true
    ; movingBoundarySmoothBeforeTStarIsTrue =
        refl
    ; q2ContradictionRouteVisible =
        true
    ; q2ContradictionRouteVisibleIsTrue =
        refl
    ; q2BlowupImplicationDischarged =
        false
    ; q2BlowupImplicationDischargedIsFalse =
        refl
    ; q2UniformBoundDischarged =
        false
    ; q2UniformBoundDischargedIsFalse =
        refl
    ; hDelta1Discharged =
        false
    ; hDelta1DischargedIsFalse =
        refl
    ; hDelta1Promoted =
        false
    ; hDelta1PromotedIsFalse =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; kornLevelSetPromoted =
        false
    ; kornLevelSetPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; receiptBoundary =
        receiptBoundaryText
    ; receiptBoundaryIsCanonical =
        refl
    }

open NSConditionalQGronwallTheoremGReceipt public

canonicalConditionalQGronwallTheoremGStageTrailIsCanonical :
  stageTrail canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ canonicalNSConditionalQGronwallTheoremGStages
canonicalConditionalQGronwallTheoremGStageTrailIsCanonical =
  refl

canonicalConditionalQGronwallTheoremGBlockerTrailIsCanonical :
  blockerTrail canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ canonicalNSConditionalQGronwallTheoremGBlockers
canonicalConditionalQGronwallTheoremGBlockerTrailIsCanonical =
  refl

canonicalConditionalQGronwallTheoremGRecordedIsCanonical :
  conditionalQGronwallTheoremGRecorded
    canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ theoremSurfaceTextValue
canonicalConditionalQGronwallTheoremGRecordedIsCanonical =
  refl

canonicalConditionalQGronwallTheoremGHDelta1HypothesisIsTrue :
  hDelta1Hypothesis canonicalNSConditionalQGronwallTheoremGReceipt ≡ true
canonicalConditionalQGronwallTheoremGHDelta1HypothesisIsTrue =
  refl

canonicalConditionalQGronwallTheoremGMuPositiveIsTrue :
  muPositive canonicalNSConditionalQGronwallTheoremGReceipt ≡ true
canonicalConditionalQGronwallTheoremGMuPositiveIsTrue =
  refl

canonicalConditionalQGronwallTheoremGMovingBoundarySmoothBeforeTStarIsTrue :
  movingBoundarySmoothBeforeTStar canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ true
canonicalConditionalQGronwallTheoremGMovingBoundarySmoothBeforeTStarIsTrue =
  refl

canonicalConditionalQGronwallTheoremGHDelta1PromotedIsFalse :
  hDelta1Promoted canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGHDelta1PromotedIsFalse =
  refl

canonicalConditionalQGronwallTheoremGCollapseImpossibleIsFalse :
  collapseImpossible canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGCollapseImpossibleIsFalse =
  refl

canonicalConditionalQGronwallTheoremGKornLevelSetPromotedIsFalse :
  kornLevelSetPromoted canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGKornLevelSetPromotedIsFalse =
  refl

canonicalConditionalQGronwallTheoremGClayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ false
canonicalConditionalQGronwallTheoremGClayNavierStokesPromotedIsFalse =
  refl

canonicalConditionalQGronwallTheoremGDependencyNamesAreCanonical :
  dependencyNames canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ canonicalNSConditionalQGronwallTheoremGDependencyNames
canonicalConditionalQGronwallTheoremGDependencyNamesAreCanonical =
  refl

canonicalConditionalQGronwallTheoremGQ2BlowupImplicationNotDischarged :
  q2BlowupImplicationDischarged canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGQ2BlowupImplicationNotDischarged =
  refl

canonicalConditionalQGronwallTheoremGQ2UniformBoundNotDischarged :
  q2UniformBoundDischarged canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGQ2UniformBoundNotDischarged =
  refl

canonicalConditionalQGronwallTheoremGQ2RouteVisible :
  q2ContradictionRouteVisible canonicalNSConditionalQGronwallTheoremGReceipt
  ≡ true
canonicalConditionalQGronwallTheoremGQ2RouteVisible =
  refl

canonicalConditionalQGronwallTheoremGHDelta1NotDischarged :
  hDelta1Discharged canonicalNSConditionalQGronwallTheoremGReceipt ≡ false
canonicalConditionalQGronwallTheoremGHDelta1NotDischarged =
  refl
