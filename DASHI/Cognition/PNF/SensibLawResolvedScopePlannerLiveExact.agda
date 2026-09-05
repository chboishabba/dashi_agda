module DASHI.Cognition.PNF.SensibLawResolvedScopePlannerLiveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawScopeCompositionLiveRegressionExact as LiveScope
import DASHI.Cognition.PNF.SensibLawConsumerIndexedDiscourseInterpretationExact as Consumer
import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing

------------------------------------------------------------------------
-- Build the higher Constitution carrier from the same live scope parser rows.
------------------------------------------------------------------------

headRow : Spacy.NumericTokenRow
headRow = Spacy.numericTokenRow LiveScope.headObservation Spacy.rootCommit

modalRow : Spacy.NumericTokenRow
modalRow =
  Spacy.numericTokenRow LiveScope.modalObservation
    (Spacy.dependencyCommit (Spacy.token LiveScope.headObservation))

scopeSyntacticProjection : Constitution.SyntacticProjectionReceipt
scopeSyntacticProjection =
  Constitution.syntacticProjectionReceipt
    headRow Constitution.complementRole
    "live scope-demo head observation"
    true true true false

scopeStructuralComposition : Constitution.StructuralCompositionReceipt
scopeStructuralComposition =
  Constitution.structuralCompositionReceipt
    scopeSyntacticProjection
    (modalRow ∷ [])
    (Constitution.sameClause ∷ [])
    "same live scope-demo parser observations"
    true false false

scopeConstitutionFibre : Constitution.SemanticCandidateFibre
scopeConstitutionFibre =
  Constitution.semanticCandidateFibre
    scopeStructuralComposition
    (Constitution.qualifierCandidate ∷ Constitution.conditionCandidate
      ∷ Constitution.temporalCandidate ∷ [])
    true true

scopePlannerState : Status.SemanticCommitmentState
scopePlannerState =
  Status.semanticCommitmentState
    scopeConstitutionFibre []
    (LiveScope.scopeDemoEvent ∷ [])
    (LiveScope.scopeDemoProposition ∷ [])
    [] true false

resolvedScopeActive : Demand.ActiveRequirement
resolvedScopeActive =
  Demand.activeRequirement
    Consumer.legalConsumer Demand.legalApplicabilityQuery
    Demand.resolvedScopeCoordinate
    Demand.legalApplicabilityNeedsResolvedScope
    "scope-demo applicability requires resolved scope"

ownedResolvedScope : Bridge.ResolvedScopeReceiptInState scopePlannerState
ownedResolvedScope =
  Bridge.resolvedScopeReceiptInState
    LiveScope.liveScopeComposition
    Bridge.here
    Bridge.here
    refl refl refl refl
    "liveScopeComposition: all modal/negation/condition/temporal scopes resolved"

resolvedScopeEvidence :
  Planner.CoordinateEvidenceReceipt scopePlannerState resolvedScopeActive
resolvedScopeEvidence =
  Bridge.resolvedScopeReceiptPaysActiveCoordinate refl ownedResolvedScope

resolvedScopePlan : Planner.RequirementPlan scopePlannerState resolvedScopeActive
resolvedScopePlan =
  Planner.planRequirement resolvedScopeEvidence
    "reuse exact same-object resolved scope receipt"

resolvedScopeReusesExisting :
  Planner.action resolvedScopePlan ≡ Planner.reuseExisting
resolvedScopeReusesExisting = refl

resolvedScopeWork : Routing.RoutedWork resolvedScopePlan
resolvedScopeWork =
  Routing.routedWork Routing.noProducerInvocation refl
    Routing.reuseWithoutProducer
    "same-object resolved scope is already paid"

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data ParserScopeCandidateWouldHaveBeenEnough : Set where
data DifferentEventScopeReceiptWouldHaveBeenEnough : Set where

parserScopeCandidateNotEnough : ParserScopeCandidateWouldHaveBeenEnough → ⊥
parserScopeCandidateNotEnough ()

differentEventScopeReceiptNotEnough : DifferentEventScopeReceiptWouldHaveBeenEnough → ⊥
differentEventScopeReceiptNotEnough ()

record ResolvedScopePlannerLiveBoundary : Set where
  constructor resolved-scope-planner-live-boundary
  field
    sameParserObjectsReused : Bool
    samePropositionRequired : Bool
    sameEventRequired : Bool
    allScopeAxesResolved : Bool
    resolvedScopeReusesExisting : Bool
    parserCandidateWouldHaveSufficed : Bool

canonicalResolvedScopePlannerLiveBoundary : ResolvedScopePlannerLiveBoundary
canonicalResolvedScopePlannerLiveBoundary =
  resolved-scope-planner-live-boundary true true true true true false
