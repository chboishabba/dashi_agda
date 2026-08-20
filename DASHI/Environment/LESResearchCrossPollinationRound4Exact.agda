module DASHI.Environment.LESResearchCrossPollinationRound4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List.Base using (length)

import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.DualEffectAdaptiveFidelityExact as Fidelity
import DASHI.Core.AssumptionIndexedReopeningExact as Reopen
import DASHI.Core.TypedTemporalExperimentExact as Temporal
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base

LESRobustEquivalentToDepth :
  ∀ {Context State Action Observation : Set} →
  Nat →
  (Context → State → Observation) →
  (Context → Action → State → State) →
  State → State → Set
LESRobustEquivalentToDepth = Refine.RobustEquivalentToDepth

LESDualEffectActionSystem : Set → Set → Set → Set₁
LESDualEffectActionSystem = Fidelity.DualEffectActionSystem

LESExperiment : Set → Set
LESExperiment = Temporal.Experiment

LESAlternativeSupportSystem : Set → Set → Set₁
LESAlternativeSupportSystem = Reopen.AlternativeSupportSystem

lesTraceSeparationRefutesBoundedEquivalence :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  (witness : Refine.TraceSeparatingWitness observe step left right) →
  Temporal.BoundedExperimentEquivalent
    (length (Refine.actions witness)) observe step left right →
  ⊥
lesTraceSeparationRefutesBoundedEquivalence = Refine.traceSeparationRefutesDepth

lesApproximateProjectionPreservesDecision :
  ∀ {Fine Coarse Output Decision}
    {project : Fine → Coarse}
    {consume : Fine → Output}
    {Within : Output → Output → Set}
    {decide : Output → Decision} →
  (descent : Refine.ApproximateConsumerDescent project consume Within) →
  Refine.ConsumerDecisionMargin Within decide →
  ∀ fine →
  decide (consume fine)
  ≡ decide (Refine.quotientConsumer descent (project fine))
lesApproximateProjectionPreservesDecision = Refine.approximateDescentPreservesDecision

record MAUPDrivenSpatialRefinement
    {Fine OldCoarse NewCoarse Result : Set}
    (oldProject : Fine → OldCoarse)
    (newProject : Fine → NewCoarse)
    (consume : Fine → Result) : Set₁ where
  constructor maupDrivenSpatialRefinement
  field
    refinement : Refine.ConsumerGuidedRefinement oldProject newProject consume
    triggerReference : String

open MAUPDrivenSpatialRefinement public

maupDrivenRefinementRefutesOldConsumerDescent :
  ∀ {Fine OldCoarse NewCoarse Result}
    {oldProject : Fine → OldCoarse}
    {newProject : Fine → NewCoarse}
    {consume : Fine → Result} →
  MAUPDrivenSpatialRefinement oldProject newProject consume →
  Base.ConsumerDescent oldProject consume →
  ⊥
maupDrivenRefinementRefutesOldConsumerDescent driven descent =
  Refine.consumerGuidedRefinementRefutesOldDescent (refinement driven) descent

lesSurvivingSupportBlocksGlobalInvalidation :
  ∀ {Change Route}
    {system : Reopen.AlternativeSupportSystem Change Route}
    {change : Change} →
  Reopen.SurvivingSupportRoute system change →
  Reopen.GloballyInvalidates system change →
  ⊥
lesSurvivingSupportBlocksGlobalInvalidation =
  Reopen.survivingRouteRefutesGlobalInvalidation

record LESRound4CrossPollinationStatus : Set where
  constructor lesRound4CrossPollinationStatus
  field
    counterexampleGuidedRefinementExtracted : Bool
    finiteTraceExperimentSeparationProved : Bool
    robustContextIndexedEquivalenceExtracted : Bool
    approximateDescentComposedWithConsumerMargin : Bool
    dualEffectWorldInformationActionsExtracted : Bool
    adaptiveFidelityDecisionSafetyExtracted : Bool
    assumptionIndexedReceiptsExtracted : Bool
    alternativeSupportRouteInvalidationExtracted : Bool
    evidenceLineageIndependenceExtracted : Bool
    typedTemporalExperimentLayerExtracted : Bool
    animalexicDomainAdapterFormalised : Bool
    domainScienceStillRequired : Bool

open LESRound4CrossPollinationStatus public

canonicalLESRound4CrossPollinationStatus : LESRound4CrossPollinationStatus
canonicalLESRound4CrossPollinationStatus =
  lesRound4CrossPollinationStatus true true true true true true true true true true true true

record LESRound4Boundary : Set where
  constructor lesRound4Boundary
  field
    refinementWitnessDoesNotChooseScientificResolutionByItself : Bool
    informationActionValueNeedsDomainCostAndRiskModel : Bool
    approximateDecisionSafetyNeedsDeclaredMargin : Bool
    robustEquivalenceNeedsDeclaredScenarioFamily : Bool
    survivingSupportRouteNeedsActualIndependentSupport : Bool
    boundedExperimentLanguageIsNotGlobalReality : Bool
    causalValidityStillNeedsScientificInterventionSemantics : Bool
    genericKernelDoesNotAuthorizeDeployment : Bool

open LESRound4Boundary public

canonicalLESRound4Boundary : LESRound4Boundary
canonicalLESRound4Boundary =
  lesRound4Boundary true true true true true true true true
