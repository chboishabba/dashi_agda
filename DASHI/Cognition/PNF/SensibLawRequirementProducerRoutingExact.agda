module DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross

data ProducerCanPopulate : Cross.ProducerClass → Demand.SemanticCoordinate → Set where
  parserPopulatesSyntax : ProducerCanPopulate Cross.parserShapeProducer Demand.syntaxCoordinate
  structurePopulatesDiscourse : ProducerCanPopulate Cross.structuralCompositionProducer Demand.discourseCoordinate
  structurePopulatesOccurrence : ProducerCanPopulate Cross.structuralCompositionProducer Demand.occurrenceCoordinate
  structurePopulatesScopeCandidate : ProducerCanPopulate Cross.structuralCompositionProducer Demand.scopeCoordinate
  bindingPopulatesReference : ProducerCanPopulate Cross.bindingAccessibilityProducer Demand.referenceCoordinate
  attributionPopulatesAttribution : ProducerCanPopulate Cross.attributionProducer Demand.attributionCoordinate
  attributionPopulatesProposition : ProducerCanPopulate Cross.attributionProducer Demand.propositionStatusCoordinate
  evidencePopulatesEvidence : ProducerCanPopulate Cross.evidenceProducer Demand.evidenceCoordinate
  evidencePopulatesProvenance : ProducerCanPopulate Cross.evidenceProducer Demand.provenanceCoordinate
  temporalPopulatesTemporal : ProducerCanPopulate Cross.temporalProducer Demand.temporalCoordinate
  documentContextPopulatesContext : ProducerCanPopulate Cross.documentContextProducer Demand.documentContextCoordinate
  legalSourcePopulatesAuthority : ProducerCanPopulate Cross.legalSourceAuthorityProducer Demand.legalSourceAuthorityCoordinate
  legalMeetPopulatesJurisdiction : ProducerCanPopulate Cross.legalTypedMeetProducer Demand.jurisdictionCoordinate
  legalMeetPopulatesLegalRole : ProducerCanPopulate Cross.legalTypedMeetProducer Demand.legalRoleCoordinate
  legalMeetPopulatesApplicability : ProducerCanPopulate Cross.legalTypedMeetProducer Demand.applicabilityCoordinate
  legalMeetPopulatesViolation : ProducerCanPopulate Cross.legalTypedMeetProducer Demand.violationCoordinate
  legalMeetPopulatesLiability : ProducerCanPopulate Cross.legalTypedMeetProducer Demand.liabilityCoordinate
  governedAdmissionPopulatesSemanticAuthority : ProducerCanPopulate Cross.governedAdmissionProducer Demand.semanticAdmissionAuthorityCoordinate

record ProducerRoute (coordinate : Demand.SemanticCoordinate) : Set where
  constructor producerRoute
  field
    producer : Cross.ProducerClass
    capability : ProducerCanPopulate producer coordinate
    routeReference : String
open ProducerRoute public

routeForActiveRequirement :
  (active : Demand.ActiveRequirement) → ProducerRoute (Demand.coordinate active) → ProducerRoute (Demand.coordinate active)
routeForActiveRequirement active route = route

data ProducerInvocationNeed : Set where
  noProducerInvocation producerInvocationRequired : ProducerInvocationNeed

invocationNeed : Planner.RequirementExecutionAction → ProducerInvocationNeed
invocationNeed Planner.inspectForEvidence = producerInvocationRequired
invocationNeed Planner.reuseExisting = noProducerInvocation
invocationNeed Planner.acquireMissingEvidence = producerInvocationRequired
invocationNeed Planner.resolveConflict = producerInvocationRequired
invocationNeed Planner.revalidateStaleEvidence = producerInvocationRequired

data WorkRoute (need : ProducerInvocationNeed) (coordinate : Demand.SemanticCoordinate) : Set where
  reuseWithoutProducer : WorkRoute noProducerInvocation coordinate
  invokeProducer : ProducerRoute coordinate → WorkRoute producerInvocationRequired coordinate

record RoutedWork {state} {active : Demand.ActiveRequirement}
    (plan : Planner.RequirementPlan state active) : Set where
  constructor routedWork
  field
    need : ProducerInvocationNeed
    needExact : need ≡ invocationNeed (Planner.action plan)
    route : WorkRoute need (Demand.coordinate active)
    routeReference : String
open RoutedWork public

referenceRoute : ProducerRoute Demand.referenceCoordinate
referenceRoute = producerRoute Cross.bindingAccessibilityProducer bindingPopulatesReference "reference/coreference candidate population"
attributionRoute : ProducerRoute Demand.attributionCoordinate
attributionRoute = producerRoute Cross.attributionProducer attributionPopulatesAttribution "source/reporting attribution producer"
temporalRoute : ProducerRoute Demand.temporalCoordinate
temporalRoute = producerRoute Cross.temporalProducer temporalPopulatesTemporal "temporal qualification/anchor producer"
documentContextRoute : ProducerRoute Demand.documentContextCoordinate
documentContextRoute = producerRoute Cross.documentContextProducer documentContextPopulatesContext "typed document/region/case context producer"
legalSourceAuthorityRoute : ProducerRoute Demand.legalSourceAuthorityCoordinate
legalSourceAuthorityRoute = producerRoute Cross.legalSourceAuthorityProducer legalSourcePopulatesAuthority "LegalSource + source system + effective interval authority producer"
semanticAdmissionAuthorityRoute : ProducerRoute Demand.semanticAdmissionAuthorityCoordinate
semanticAdmissionAuthorityRoute = producerRoute Cross.governedAdmissionProducer governedAdmissionPopulatesSemanticAuthority "semantic resolution/admission authority producer"
applicabilityRoute : ProducerRoute Demand.applicabilityCoordinate
applicabilityRoute = producerRoute Cross.legalTypedMeetProducer legalMeetPopulatesApplicability "typed legal applicability meet"

data ReuseExistingRequiresProducerInvocation : Set where
data UnassessedRequirementMaySkipInspectionProducer : Set where
data ParserCanPopulateLegalApplicability : Set where
data AttributionProducerCanResolveLegalSourceAuthority : Set where
data SemanticAdmissionProducerCanResolveLegalSourceAuthority : Set where
data DocumentContextIsParserShape : Set where

actionReuseNeedsNoProducer : invocationNeed Planner.reuseExisting ≡ noProducerInvocation
actionReuseNeedsNoProducer = refl
inspectionNeedsProducer : invocationNeed Planner.inspectForEvidence ≡ producerInvocationRequired
inspectionNeedsProducer = refl
missingEvidenceNeedsProducer : invocationNeed Planner.acquireMissingEvidence ≡ producerInvocationRequired
missingEvidenceNeedsProducer = refl
reuseHasLiteralNoProducerRoute : ∀ {coordinate} → WorkRoute noProducerInvocation coordinate
reuseHasLiteralNoProducerRoute = reuseWithoutProducer
reuseDoesNotInvokeProducer : ReuseExistingRequiresProducerInvocation → ⊥
reuseDoesNotInvokeProducer ()
unassessedRequirementCannotSkipInspectionProducer : UnassessedRequirementMaySkipInspectionProducer → ⊥
unassessedRequirementCannotSkipInspectionProducer ()
parserDoesNotOwnLegalApplicability : ParserCanPopulateLegalApplicability → ⊥
parserDoesNotOwnLegalApplicability ()
attributionDoesNotOwnLegalSourceAuthority : AttributionProducerCanResolveLegalSourceAuthority → ⊥
attributionDoesNotOwnLegalSourceAuthority ()
semanticAdmissionDoesNotOwnLegalSourceAuthority : SemanticAdmissionProducerCanResolveLegalSourceAuthority → ⊥
semanticAdmissionDoesNotOwnLegalSourceAuthority ()
documentContextDoesNotCollapseToParserShape : DocumentContextIsParserShape → ⊥
documentContextDoesNotCollapseToParserShape ()

record RequirementProducerRoutingBoundary : Set where
  constructor requirement-producer-routing-boundary
  field
    producerRoutingIsCoordinateIndexed : Bool
    unassessedRequirementNeedsInspectionProducer : Bool
    satisfiedRequirementNeedsProducerInvocation : Bool
    parserMayPopulateLegalApplicability : Bool
    attributionMayResolveLegalSourceAuthority : Bool
    semanticAdmissionMayResolveLegalSourceAuthority : Bool
    legalSourceAuthorityHasDedicatedProducerClass : Bool
    documentContextHasDedicatedProducerClass : Bool
canonicalRequirementProducerRoutingBoundary : RequirementProducerRoutingBoundary
canonicalRequirementProducerRoutingBoundary = requirement-producer-routing-boundary true true false false false false true true
