module DASHI.Biology.CausalHierarchicalChartResidualExact where

open import DASHI.Core.Prelude
open import DASHI.Biology.TriadicKernelLiftQuotientExact

------------------------------------------------------------------------
-- A causal chart consumes only the history available before the target.  The
-- target is a separate input used solely to score the residual.  This type
-- separation prevents the predicted value from depending on the value being
-- predicted.

record HistoryTwo : Set where
  constructor historyTwo
  field
    previousTwo : Nat
    previousOne : Nat

open HistoryTwo public

Predictor : Set
Predictor = HistoryTwo → Nat

lastValuePredictor : Predictor
lastValuePredictor history = previousOne history

record ForecastCase : Set where
  constructor forecastCase
  field
    history : HistoryTwo
    target : Nat

open ForecastCase public

prediction : Predictor → ForecastCase → Nat
prediction predictor sample = predictor (history sample)

natResidual : Nat → Nat → Nat
natResidual predicted observed =
  (predicted ∸ observed) + (observed ∸ predicted)

forecastResidual : Predictor → ForecastCase → Nat
forecastResidual predictor sample =
  natResidual (prediction predictor sample) (target sample)

sharedHistory : HistoryTwo
sharedHistory = historyTwo 3 5

matchedTargetCase : ForecastCase
matchedTargetCase = forecastCase sharedHistory 5

shiftedTargetCase : ForecastCase
shiftedTargetCase = forecastCase sharedHistory 7

sameHistoryHasSamePrediction :
  prediction lastValuePredictor matchedTargetCase
  ≡
  prediction lastValuePredictor shiftedTargetCase
sameHistoryHasSamePrediction = refl

matchedResidualIsZero :
  forecastResidual lastValuePredictor matchedTargetCase ≡ 0
matchedResidualIsZero = refl

shiftedResidualIsTwo :
  forecastResidual lastValuePredictor shiftedTargetCase ≡ 2
shiftedResidualIsTwo = refl

------------------------------------------------------------------------
-- Exact finite partition refinement.  Domain depth and triadic value depth
-- are separate indices.

data CoarseBlock : Set where
  leftBlock : CoarseBlock
  rightBlock : CoarseBlock

data FineBlock : Set where
  leftLower : FineBlock
  leftUpper : FineBlock
  rightLower : FineBlock
  rightUpper : FineBlock

parentBlock : FineBlock → CoarseBlock
parentBlock leftLower = leftBlock
parentBlock leftUpper = leftBlock
parentBlock rightLower = rightBlock
parentBlock rightUpper = rightBlock

data LocalTransform : Set where
  keepTransform : LocalTransform
  incrementTransform : LocalTransform
  decrementTransform : LocalTransform

applyTransform : LocalTransform → Nat → Nat
applyTransform keepTransform x = x
applyTransform incrementTransform x = suc x
applyTransform decrementTransform zero = zero
applyTransform decrementTransform (suc x) = x

record CoarseChart : Set where
  constructor coarseChart
  field
    leftTransform : LocalTransform
    rightTransform : LocalTransform

open CoarseChart public

applyCoarseChart : CoarseChart → CoarseBlock → Nat → Nat
applyCoarseChart chart leftBlock x = applyTransform (leftTransform chart) x
applyCoarseChart chart rightBlock x = applyTransform (rightTransform chart) x

canonicalCoarseChart : CoarseChart
canonicalCoarseChart = coarseChart incrementTransform decrementTransform

leftChartIncrements : applyCoarseChart canonicalCoarseChart leftBlock 5 ≡ 6
leftChartIncrements = refl

rightChartDecrements : applyCoarseChart canonicalCoarseChart rightBlock 5 ≡ 4
rightChartDecrements = refl

------------------------------------------------------------------------
-- A small balanced-ternary depth functional.  The cut points are the exact
-- one-, two-, and three-digit balanced ranges: 1, 4, and 13.  The finite
-- surface below is sufficient for the concrete candidate comparison.

residualDepth3 : Nat → Nat
residualDepth3 0 = 0
residualDepth3 1 = 1
residualDepth3 2 = 2
residualDepth3 3 = 2
residualDepth3 4 = 2
residualDepth3 5 = 3
residualDepth3 (suc (suc (suc (suc (suc (suc n)))))) = 3

data ChartCandidate : Set where
  coarseCandidate : ChartCandidate
  refinedCandidate : ChartCandidate

chartComplexity : ChartCandidate → Nat
chartComplexity coarseCandidate = 1
chartComplexity refinedCandidate = 2

candidateResidualMagnitude : ChartCandidate → Nat
candidateResidualMagnitude coarseCandidate = 5
candidateResidualMagnitude refinedCandidate = 1

candidateObjective : ChartCandidate → Nat
candidateObjective candidate =
  chartComplexity candidate
  +
  residualDepth3 (candidateResidualMagnitude candidate)

coarseObjectiveIsFour : candidateObjective coarseCandidate ≡ 4
coarseObjectiveIsFour = refl

refinedObjectiveIsThree : candidateObjective refinedCandidate ≡ 3
refinedObjectiveIsThree = refl

refinedCandidateIsMinimal :
  (candidate : ChartCandidate) →
  candidateObjective refinedCandidate ≤ candidateObjective candidate
refinedCandidateIsMinimal coarseCandidate = s≤s (s≤s (s≤s z≤n))
refinedCandidateIsMinimal refinedCandidate = ≤-refl

------------------------------------------------------------------------
-- Finite consistency tube.  Two depth-two states lie in the same coarse
-- cylinder exactly when their first trit agrees; the second trit remains an
-- unresolved fine coordinate.

record DepthTwoKernelState : Set where
  constructor depthTwoKernelState
  field
    coarseTrit : KernelTrit
    fineTrit : KernelTrit

open DepthTwoKernelState public

SameCoarseCylinder : DepthTwoKernelState → DepthTwoKernelState → Set
SameCoarseCylinder x y = coarseTrit x ≡ coarseTrit y

stateA : DepthTwoKernelState
stateA = depthTwoKernelState positiveTrit negativeTrit

stateB : DepthTwoKernelState
stateB = depthTwoKernelState positiveTrit positiveTrit

stateC : DepthTwoKernelState
stateC = depthTwoKernelState negativeTrit positiveTrit

sameCylinderDifferentFineState :
  SameCoarseCylinder stateA stateB
sameCylinderDifferentFineState = refl

record CausalChartBoundary : Set where
  constructor causalChartBoundary
  field
    predictorMayReadCurrentTarget : Bool
    predictorMayReadCurrentTargetIsFalse :
      predictorMayReadCurrentTarget ≡ false

    partitionDepthEqualsValueDepth : Bool
    partitionDepthEqualsValueDepthIsFalse :
      partitionDepthEqualsValueDepth ≡ false

    consistencyTubeIsAssertedDifferentiableManifold : Bool
    consistencyTubeIsAssertedDifferentiableManifoldIsFalse :
      consistencyTubeIsAssertedDifferentiableManifold ≡ false

    objectiveMinimalityImpliesGlobalSearchIsLinearTime : Bool
    objectiveMinimalityImpliesGlobalSearchIsLinearTimeIsFalse :
      objectiveMinimalityImpliesGlobalSearchIsLinearTime ≡ false

open CausalChartBoundary public

canonicalCausalChartBoundary : CausalChartBoundary
canonicalCausalChartBoundary =
  causalChartBoundary false refl false refl false refl false refl
