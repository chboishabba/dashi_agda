module DASHI.Dynamics.EvidenceGatedRechartBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Dynamics.TriadicResidualRechartDynamics as Residual
import DASHI.Foundations.JChartSuccessorBoundary as Charts

data RechartEvidence : Set where
  stableEvidence refinableWithinChartEvidence gluingDefectEvidence : RechartEvidence
  mdlImprovementEvidence gluingAndMDLEvidence : RechartEvidence

data RechartDecision : Set where
  retainChartDecision refineChartDecision successorChartDecision : RechartDecision

decideRechart : RechartEvidence → RechartDecision
decideRechart stableEvidence = retainChartDecision
decideRechart refinableWithinChartEvidence = refineChartDecision
decideRechart gluingDefectEvidence = successorChartDecision
decideRechart mdlImprovementEvidence = successorChartDecision
decideRechart gluingAndMDLEvidence = successorChartDecision

residualEvidence : Residual.ResidualKind → RechartEvidence
residualEvidence Residual.negligibleResidual = stableEvidence
residualEvidence Residual.harmonicResidual = refinableWithinChartEvidence
residualEvidence Residual.fineScaleResidual = refinableWithinChartEvidence
residualEvidence Residual.gluingFailureResidual = gluingDefectEvidence

applyDecision : Charts.ChartIndex → RechartDecision → Charts.ChartIndex
applyDecision current retainChartDecision = current
applyDecision current refineChartDecision = current
applyDecision current successorChartDecision = Charts.nextChart current

chartTenGluingFailureGoesToEleven :
  applyDecision (Charts.chart 10) (decideRechart gluingDefectEvidence) ≡ Charts.chart 11
chartTenGluingFailureGoesToEleven = refl

chartTenRefinementStaysAtTen :
  applyDecision (Charts.chart 10) (decideRechart refinableWithinChartEvidence) ≡ Charts.chart 10
chartTenRefinementStaysAtTen = refl

record RechartEvidenceReceipt : Set where
  constructor rechartEvidenceReceipt
  field
    currentChart : Charts.ChartIndex
    evidence : RechartEvidence
    selectedDecision : RechartDecision
    selectedDecisionChecks : selectedDecision ≡ decideRechart evidence
    resultChart : Charts.ChartIndex
    resultChecks : resultChart ≡ applyDecision currentChart selectedDecision
    interpretation : String

canonicalGluingFailureReceipt : RechartEvidenceReceipt
canonicalGluingFailureReceipt =
  rechartEvidenceReceipt (Charts.chart 10) gluingDefectEvidence successorChartDecision refl
    (Charts.chart 11) refl
    "an explicit gluing failure at chart 10 permits the typed successor chart 11"

record RechartMetricLane : Set₁ where
  field
    Score : Set
    _<_ : Score → Score → Set
    gluingScore gluingThreshold currentMDL candidateMDL complexityMargin : Score
    gluingFailureProved candidatePaysForRechart : Set

record EvidenceGatedRechartBoundary : Set where
  constructor evidenceGatedRechartBoundary
  field
    frameRecognitionAloneTriggersRechart : Bool
    frameRecognitionAloneTriggersRechartIsFalse : frameRecognitionAloneTriggersRechart ≡ false
    refinableResidualForcesSuccessorChart : Bool
    refinableResidualForcesSuccessorChartIsFalse : refinableResidualForcesSuccessorChart ≡ false
    gluingOrMDLEvidenceRequired jPlusOneAvailableAfterReceipt : Bool
    everyGluingDefectRequiresImmediateRechart : Bool
    everyGluingDefectRequiresImmediateRechartIsFalse : everyGluingDefectRequiresImmediateRechart ≡ false
    interpretation : String

canonicalEvidenceGatedRechartBoundary : EvidenceGatedRechartBoundary
canonicalEvidenceGatedRechartBoundary =
  evidenceGatedRechartBoundary
    false refl
    false refl
    true true
    false refl
    "retain, refine, and successor rechart are separate actions; frame awareness does not imply failure, and j+1 requires a gluing or MDL receipt"
