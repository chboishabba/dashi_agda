module DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorStateBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as Typed
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Physics.ExoticGravity.LiTorrStandardGRComparatorBidiExact as Legacy

------------------------------------------------------------------------
-- SAME-OBJECT BRIDGE: NEW TYPED SOURCE/GR REQUEST -> EXISTING COMPARATOR STATE
--
-- The optimized plan already owns the planning state (1,1,1,1,0,0) after a
-- full source/geometry bundle.  This owner binds that state to the new typed
-- laboratory GR evaluation request, then binds an actual numerical prediction
-- receipt to the next state (1,1,1,1,1,0).  Background closure remains a
-- separate consumer and is not inferred from the prediction.
------------------------------------------------------------------------

requestStageState : Legacy.GRComparatorState
requestStageState =
  Legacy.gr-comparator-state true true true true false false

requestStageMatchesExistingPlan :
  requestStageState ≡ Plan.postSourceComparatorState
requestStageMatchesExistingPlan = refl

requestStageFirstOpen :
  Legacy.firstOpenGRComparatorLeaf requestStageState
    ≡ Legacy.weakFieldSolverLeaf
requestStageFirstOpen = refl

predictionStageState : Legacy.GRComparatorState
predictionStageState =
  Legacy.gr-comparator-state true true true true true false

predictionStageFirstOpen :
  Legacy.firstOpenGRComparatorLeaf predictionStageState
    ≡ Legacy.backgroundClosureLeaf
predictionStageFirstOpen = refl

record TypedRequestStateWeld
    (request : Typed.OrdinaryGREvaluationRequest) : Set where
  constructor typed-request-state-weld
  field
    state : Legacy.GRComparatorState
    stateMatchesRequestStage : state ≡ requestStageState
    exactTypedRequest : Typed.OrdinaryGREvaluationRequest
    exactTypedRequestMatches : exactTypedRequest ≡ request

open TypedRequestStateWeld public

compileRequestStateWeld :
  (request : Typed.OrdinaryGREvaluationRequest) →
  TypedRequestStateWeld request
compileRequestStateWeld request =
  typed-request-state-weld requestStageState refl request refl

record TypedPredictionStateWeld
    (prediction : Typed.OrdinaryGRPredictionReceipt) : Set where
  constructor typed-prediction-state-weld
  field
    state : Legacy.GRComparatorState
    stateMatchesPredictionStage : state ≡ predictionStageState
    exactPrediction : Typed.OrdinaryGRPredictionReceipt
    exactPredictionMatches : exactPrediction ≡ prediction
    exactRequest : Typed.OrdinaryGREvaluationRequest
    exactRequestMatchesPrediction :
      exactRequest ≡ Typed.request prediction

open TypedPredictionStateWeld public

compilePredictionStateWeld :
  (prediction : Typed.OrdinaryGRPredictionReceipt) →
  TypedPredictionStateWeld prediction
compilePredictionStateWeld prediction =
  typed-prediction-state-weld
    predictionStageState refl
    prediction refl
    (Typed.request prediction) refl

------------------------------------------------------------------------
-- Introspective non-collapse.
------------------------------------------------------------------------

record LaboratoryGRComparatorStateBridgeBoundary : Set where
  constructor laboratory-gr-comparator-state-bridge-boundary
  field
    planningStateAloneCreatesTypedRequest : Bool
    typedRequestPaysWeakFieldPrediction : Bool
    typedPredictionPaysWeakFieldPredictionState : Bool
    typedPredictionPaysBackgroundClosure : Bool
    backgroundClosureRemainsSeparateAfterPrediction : Bool
    requestStateEqualsPredictionState : Bool
    existingPlanningStateReusedRatherThanForked : Bool

canonicalLaboratoryGRComparatorStateBridgeBoundary :
  LaboratoryGRComparatorStateBridgeBoundary
canonicalLaboratoryGRComparatorStateBridgeBoundary =
  laboratory-gr-comparator-state-bridge-boundary
    false false true false true false true
