module DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand

data CoordinateEvidenceDisposition : Set where
  currentResolved currentMissing currentConflicting stalePreviouslyResolved
  : CoordinateEvidenceDisposition

data RequirementDisposition : Set where
  alreadySatisfied missingEvidence conflictingEvidence reopenRequired
  : RequirementDisposition

data RequirementExecutionAction : Set where
  reuseExisting acquireMissingEvidence resolveConflict revalidateStaleEvidence
  : RequirementExecutionAction

record CoordinateEvidenceReceipt
    (state : Status.SemanticCommitmentState)
    (active : Demand.ActiveRequirement) : Set where
  constructor coordinateEvidenceReceipt
  field
    evidenceDisposition : CoordinateEvidenceDisposition
    evidenceReferences : List String
    producerReference : String
    sourceCandidatePreserved : Bool
    sourceCandidatePreservedIsTrue : sourceCandidatePreserved ≡ true
    coordinateOnly : Bool
    coordinateOnlyIsTrue : coordinateOnly ≡ true
open CoordinateEvidenceReceipt public

classifyEvidence : CoordinateEvidenceDisposition → RequirementDisposition
classifyEvidence currentResolved = alreadySatisfied
classifyEvidence currentMissing = missingEvidence
classifyEvidence currentConflicting = conflictingEvidence
classifyEvidence stalePreviouslyResolved = reopenRequired

leastAction : RequirementDisposition → RequirementExecutionAction
leastAction alreadySatisfied = reuseExisting
leastAction missingEvidence = acquireMissingEvidence
leastAction conflictingEvidence = resolveConflict
leastAction reopenRequired = revalidateStaleEvidence

record RequirementPlan
    (state : Status.SemanticCommitmentState)
    (active : Demand.ActiveRequirement) : Set where
  constructor requirementPlan
  field
    evidence : CoordinateEvidenceReceipt state active
    disposition : RequirementDisposition
    dispositionExact : disposition ≡ classifyEvidence (evidenceDisposition evidence)
    action : RequirementExecutionAction
    actionExact : action ≡ leastAction disposition
    activeCoordinate : Demand.SemanticCoordinate
    activeCoordinateExact : activeCoordinate ≡ Demand.coordinate active
    parserReparseRequired : Bool
    parserReparseRequiredIsFalse : parserReparseRequired ≡ false
    planReference : String
open RequirementPlan public

planRequirement :
  {state : Status.SemanticCommitmentState} →
  {active : Demand.ActiveRequirement} →
  CoordinateEvidenceReceipt state active → String → RequirementPlan state active
planRequirement {active = active} receipt ref =
  requirementPlan receipt
    (classifyEvidence (evidenceDisposition receipt)) refl
    (leastAction (classifyEvidence (evidenceDisposition receipt))) refl
    (Demand.coordinate active) refl false refl ref

record PlannedRequirement (state : Status.SemanticCommitmentState) : Set where
  constructor plannedRequirement
  field
    active : Demand.ActiveRequirement
    plan : RequirementPlan state active
open PlannedRequirement public

record DemandExecutionPlan
    (state : Status.SemanticCommitmentState)
    (demand : Demand.SemanticDemand) : Set where
  constructor demandExecutionPlan
  field
    planned : List (PlannedRequirement state)
    demandReferencePreserved : String
    plannerReference : String
    underlyingStateRewritten : Bool
    underlyingStateRewrittenIsFalse : underlyingStateRewritten ≡ false
open DemandExecutionPlan public

resolvedReceiptGivesSatisfied :
  ∀ {state active refs producer} →
  disposition (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentResolved refs producer true refl true refl)
    "resolved") ≡ alreadySatisfied
resolvedReceiptGivesSatisfied = refl

resolvedReceiptReusesExisting :
  ∀ {state active refs producer} →
  action (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentResolved refs producer true refl true refl)
    "resolved") ≡ reuseExisting
resolvedReceiptReusesExisting = refl

missingReceiptGivesMissing :
  ∀ {state active refs producer} →
  disposition (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentMissing refs producer true refl true refl)
    "missing") ≡ missingEvidence
missingReceiptGivesMissing = refl

missingReceiptAcquiresEvidence :
  ∀ {state active refs producer} →
  action (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentMissing refs producer true refl true refl)
    "missing") ≡ acquireMissingEvidence
missingReceiptAcquiresEvidence = refl

conflictingReceiptGivesConflict :
  ∀ {state active refs producer} →
  disposition (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentConflicting refs producer true refl true refl)
    "conflicting") ≡ conflictingEvidence
conflictingReceiptGivesConflict = refl

conflictingReceiptResolvesConflict :
  ∀ {state active refs producer} →
  action (planRequirement
    (coordinateEvidenceReceipt {state} {active} currentConflicting refs producer true refl true refl)
    "conflicting") ≡ resolveConflict
conflictingReceiptResolvesConflict = refl

staleReceiptGivesReopening :
  ∀ {state active refs producer} →
  disposition (planRequirement
    (coordinateEvidenceReceipt {state} {active} stalePreviouslyResolved refs producer true refl true refl)
    "stale") ≡ reopenRequired
staleReceiptGivesReopening = refl

staleReceiptRevalidatesOnly :
  ∀ {state active refs producer} →
  action (planRequirement
    (coordinateEvidenceReceipt {state} {active} stalePreviouslyResolved refs producer true refl true refl)
    "stale") ≡ revalidateStaleEvidence
staleReceiptRevalidatesOnly = refl

data SemanticStateAloneTotalizesCoordinateEvidence : Set where
data ResolvedOtherCoordinateFillsMissingActiveRequirement : Set where
data StaleReceiptStillCountsAsSatisfied : Set where
data ConflictingReceiptCountsAsMissing : Set where
data PlanningRequirementRewritesSemanticState : Set where
data PlanningRequirementRequiresParserReparse : Set where
data SatisfiedRequirementRecomputesProducer : Set where
data StaleRequirementForcesFullReparse : Set where

semanticStateAloneDoesNotTotalizeEvidence : SemanticStateAloneTotalizesCoordinateEvidence → ⊥
semanticStateAloneDoesNotTotalizeEvidence ()
resolvedOtherCoordinateDoesNotFillMissingRequirement : ResolvedOtherCoordinateFillsMissingActiveRequirement → ⊥
resolvedOtherCoordinateDoesNotFillMissingRequirement ()
staleReceiptDoesNotRemainSatisfied : StaleReceiptStillCountsAsSatisfied → ⊥
staleReceiptDoesNotRemainSatisfied ()
conflictDoesNotCollapseToMissing : ConflictingReceiptCountsAsMissing → ⊥
conflictDoesNotCollapseToMissing ()
planningDoesNotRewriteState : PlanningRequirementRewritesSemanticState → ⊥
planningDoesNotRewriteState ()
planningDoesNotRequireParserReparse : PlanningRequirementRequiresParserReparse → ⊥
planningDoesNotRequireParserReparse ()
satisfiedRequirementDoesNotRecomputeProducer : SatisfiedRequirementRecomputesProducer → ⊥
satisfiedRequirementDoesNotRecomputeProducer ()
staleRequirementDoesNotForceFullReparse : StaleRequirementForcesFullReparse → ⊥
staleRequirementDoesNotForceFullReparse ()

record ActiveRequirementExecutionPlannerBoundary : Set where
  constructor active-requirement-execution-planner-boundary
  field
    planningIsIndexedByExactActiveRequirement : Bool
    semanticStateAloneIsTotalEvidenceOracle : Bool
    missingAndConflictingRemainDistinct : Bool
    stalePreviouslyResolvedReopens : Bool
    satisfiedRequirementReusesExistingEvidence : Bool
    missingRequirementAcquiresOnlyMissingEvidence : Bool
    conflictGetsDistinctResolutionAction : Bool
    staleRequirementUsesRevalidationAction : Bool
    oneCoordinateCanCompensateForAnother : Bool
    planningRewritesUnderlyingState : Bool
    planningRequiresParserReparse : Bool
canonicalActiveRequirementExecutionPlannerBoundary : ActiveRequirementExecutionPlannerBoundary
canonicalActiveRequirementExecutionPlannerBoundary =
  active-requirement-execution-planner-boundary true false true true true true true true false false false
