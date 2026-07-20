module DASHI.Environment.InversePlanning where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_+_; _≤_)

import DASHI.Environment.FunctionalEcology as Eco
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Foundations.SSPTritCarrier as SSP

------------------------------------------------------------------------
-- Observations and source hypotheses.

record Observation : Set where
  constructor mkObservation
  field
    observationName : String
    locationLabel : String
    timeLabel : String
    observedDirection : SSP.SSPTrit
    evidenceDepth : Nat
    measurementUncertainty : Nat
open Observation public

record SourceHypothesis : Set where
  constructor mkSourceHypothesis
  field
    hypothesisName : String
    sourceLocation : String
    sourceGroup : Eco.FunctionalGroup
    transportPathRecorded : Bool
    timingCompatible : Bool
    mechanismRecorded : Bool
    priorCost : Nat
open SourceHypothesis public

record Explanation : Set where
  constructor mkExplanation
  field
    source : SourceHypothesis
    target : Observation
    predictedDirection : SSP.SSPTrit
    residualCost : Nat
    transportCost : Nat
    complexityCost : Nat
    lane : Latent.ModelLane
    supportingEvidence : List String
open Explanation public

explanationCost : Explanation → Nat
explanationCost e = residualCost e + transportCost e + complexityCost e

record RankedExplanation (chosen : Explanation)
                         (alternatives : List Explanation) : Set where
  constructor mkRankedExplanation
  field
    candidateSetRecorded : Bool
    chosenIsAdmissible : Bool
    noCheaperAdmissibleAlternative :
      ∀ alternative →
      alternative ∈ alternatives →
      explanationCost chosen ≤ explanationCost alternative
    uncertaintyDisclosed : Bool
    attributionIsHypothesisNotBlame : Bool
open RankedExplanation public

------------------------------------------------------------------------
-- Forward planning.

data ObjectiveKind : Set where
  waterInfiltration : ObjectiveKind
  erosionReduction : ObjectiveKind
  nutrientRetention : ObjectiveKind
  habitatSupport : ObjectiveKind
  threatenedSpeciesSupport : ObjectiveKind
  pollinationService : ObjectiveKind
  nativePollinatorProtection : ObjectiveKind
  soilCarbon : ObjectiveKind
  yieldStability : ObjectiveKind
  farmProfit : ObjectiveKind
  labourMinimisation : ObjectiveKind
  machineryFeasibility : ObjectiveKind
  fuelUseReduction : ObjectiveKind
  climateResilience : ObjectiveKind

record Objective : Set where
  constructor mkObjective
  field
    objectiveName : String
    kind : ObjectiveKind
    desiredDirection : SSP.SSPTrit
    weight : Nat
    policyCritical : Bool
open Objective public

record Constraint : Set where
  constructor mkConstraint
  field
    constraintName : String
    satisfied : Bool
    hardConstraint : Bool
    evidenceLabel : String
open Constraint public

record Plan : Set where
  constructor mkPlan
  field
    planName : String
    interventions : List Eco.Intervention
    objectives : List Objective
    constraints : List Constraint
    lane : Latent.ModelLane
    residualCost : Nat
    interventionCost : Nat
    modelComplexityCost : Nat
    uncertaintyCost : Nat
open Plan public

planCost : Plan → Nat
planCost p =
  residualCost p
  + interventionCost p
  + modelComplexityCost p
  + uncertaintyCost p

record ParetoWitness (candidate : Plan) : Set where
  constructor mkParetoWitness
  field
    allHardConstraintsSatisfied : Bool
    noClaimOfUniqueOptimum : Bool
    tradeoffsRecorded : List String
    uncertaintyRecorded : Bool
open ParetoWitness public

------------------------------------------------------------------------
-- Adaptive model-depth receipt.

record PlanningReceipt : Set where
  constructor mkPlanningReceipt
  field
    selectedPlan : Plan
    modelLaneUsed : Latent.ModelLane
    escalationEvidence : Latent.EscalationEvidence
    resultingLane : Latent.ModelLane
    resultingLaneMatches :
      resultingLane ≡ Latent.chooseLane modelLaneUsed escalationEvidence
    assumptions : List String
    exclusions : List String
    provenance : List String
    humanApprovalRequired : Bool
open PlanningReceipt public

canonicalScreeningReceipt : Plan → PlanningReceipt
canonicalScreeningReceipt p =
  mkPlanningReceipt
    p
    Latent.pathA-screening
    (Latent.mkEscalationEvidence false false false false false)
    Latent.pathA-screening
    refl
    ("screening-only" ∷ [])
    ("not a final engineering or ecological approval" ∷ [])
    ("typed DASHI environment planning receipt" ∷ [])
    true

------------------------------------------------------------------------
-- Governance boundary for pollution and policy use.

record InversePlanningBoundary : Set where
  constructor mkInversePlanningBoundary
  field
    sourceRankingIsNotLegalAttribution : Bool
    correlationIsNotCausation : Bool
    missingSourcesRemainPossible : Bool
    transportModelMustBeAuditable : Bool
    policyCriticalResultsEscalate : Bool
    humanAndCommunityJudgementRequired : Bool
open InversePlanningBoundary public

canonicalInversePlanningBoundary : InversePlanningBoundary
canonicalInversePlanningBoundary =
  mkInversePlanningBoundary true true true true true true

inversePlanningSummary : String
inversePlanningSummary =
  "Observed degradation or pollution is matched to auditable source hypotheses by residual, transport, and complexity cost; intervention plans remain constrained multi-objective candidates with A/B/C escalation, provenance, uncertainty, and mandatory human approval."
