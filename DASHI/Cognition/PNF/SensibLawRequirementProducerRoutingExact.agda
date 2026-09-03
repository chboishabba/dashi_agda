module DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawConsumerQuerySemanticCoordinateReopeningExact as Demand
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross

------------------------------------------------------------------------
-- REQUIREMENT -> PRODUCER ROUTING
--
-- A planner action does not authorize an arbitrary producer.  Routing is
-- indexed by semantic coordinate and producer capability.  The existing
-- SensibLaw ProducerClass taxonomy is reused rather than inventing a second
-- semantic producer ontology.
------------------------------------------------------------------------

data ProducerCanPopulate :
    Cross.ProducerClass → Demand.SemanticCoordinate → Set where
  parserPopulatesSyntax :
    ProducerCanPopulate Cross.parserShapeProducer Demand.syntaxCoordinate

  structurePopulatesDiscourse :
    ProducerCanPopulate Cross.structuralCompositionProducer Demand.discourseCoordinate
  structurePopulatesOccurrence :
    ProducerCanPopulate Cross.structuralCompositionProducer Demand.occurrenceCoordinate
  structurePopulatesScopeCandidate :
    ProducerCanPopulate Cross.structuralCompositionProducer Demand.scopeCoordinate

  bindingPopulatesReference :
    ProducerCanPopulate Cross.bindingAccessibilityProducer Demand.referenceCoordinate

  attributionPopulatesAttribution :
    ProducerCanPopulate Cross.attributionProducer Demand.attributionCoordinate
  attributionPopulatesProposition :
    ProducerCanPopulate Cross.attributionProducer Demand.propositionStatusCoordinate

  evidencePopulatesEvidence :
    ProducerCanPopulate Cross.evidenceProducer Demand.evidenceCoordinate
  evidencePopulatesProvenance :
    ProducerCanPopulate Cross.evidenceProducer Demand.provenanceCoordinate

  temporalPopulatesTemporal :
    ProducerCanPopulate Cross.temporalProducer Demand.temporalCoordinate

  documentContextPopulatesContext :
    ProducerCanPopulate Cross.documentContextProducer Demand.documentContextCoordinate

  legalMeetPopulatesJurisdiction :
    ProducerCanPopulate Cross.legalTypedMeetProducer Demand.jurisdictionCoordinate
  legalMeetPopulatesLegalRole :
    ProducerCanPopulate Cross.legalTypedMeetProducer Demand.legalRoleCoordinate
  legalMeetPopulatesApplicability :
    ProducerCanPopulate Cross.legalTypedMeetProducer Demand.applicabilityCoordinate
  legalMeetPopulatesViolation :
    ProducerCanPopulate Cross.legalTypedMeetProducer Demand.violationCoordinate
  legalMeetPopulatesLiability :
    ProducerCanPopulate Cross.legalTypedMeetProducer Demand.liabilityCoordinate

  governedAdmissionPopulatesAuthority :
    ProducerCanPopulate Cross.governedAdmissionProducer Demand.authorityCoordinate

record ProducerRoute (coordinate : Demand.SemanticCoordinate) : Set where
  constructor producerRoute
  field
    producer : Cross.ProducerClass
    capability : ProducerCanPopulate producer coordinate
    routeReference : String

open ProducerRoute public

routeForActiveRequirement :
  (active : Demand.ActiveRequirement) →
  ProducerRoute (Demand.coordinate active) →
  ProducerRoute (Demand.coordinate active)
routeForActiveRequirement active route = route

------------------------------------------------------------------------
-- Work routing distinguishes reuse from producer invocation.
------------------------------------------------------------------------

data ProducerInvocationNeed : Set where
  noProducerInvocation
  producerInvocationRequired
  : ProducerInvocationNeed

invocationNeed : Planner.RequirementExecutionAction → ProducerInvocationNeed
invocationNeed Planner.reuseExisting = noProducerInvocation
invocationNeed Planner.acquireMissingEvidence = producerInvocationRequired
invocationNeed Planner.resolveConflict = producerInvocationRequired
invocationNeed Planner.revalidateStaleEvidence = producerInvocationRequired

data WorkRoute
    (need : ProducerInvocationNeed)
    (coordinate : Demand.SemanticCoordinate) : Set where
  reuseWithoutProducer : WorkRoute noProducerInvocation coordinate
  invokeProducer :
    ProducerRoute coordinate →
    WorkRoute producerInvocationRequired coordinate

record RoutedWork
    {state}
    {active : Demand.ActiveRequirement}
    (plan : Planner.RequirementPlan state active) : Set where
  constructor routedWork
  field
    need : ProducerInvocationNeed
    needExact : need ≡ invocationNeed (Planner.action plan)
    route : WorkRoute need (Demand.coordinate active)
    routeReference : String

open RoutedWork public

------------------------------------------------------------------------
-- Canonical coordinate routes.
------------------------------------------------------------------------

referenceRoute : ProducerRoute Demand.referenceCoordinate
referenceRoute = producerRoute Cross.bindingAccessibilityProducer bindingPopulatesReference
  "reference/coreference candidate population"

attributionRoute : ProducerRoute Demand.attributionCoordinate
attributionRoute = producerRoute Cross.attributionProducer attributionPopulatesAttribution
  "source/reporting attribution producer"

temporalRoute : ProducerRoute Demand.temporalCoordinate
temporalRoute = producerRoute Cross.temporalProducer temporalPopulatesTemporal
  "temporal qualification/anchor producer"

documentContextRoute : ProducerRoute Demand.documentContextCoordinate
documentContextRoute = producerRoute Cross.documentContextProducer documentContextPopulatesContext
  "typed document/region/case context producer"

authorityRoute : ProducerRoute Demand.authorityCoordinate
authorityRoute = producerRoute Cross.governedAdmissionProducer governedAdmissionPopulatesAuthority
  "governed authority/admission evidence producer"

applicabilityRoute : ProducerRoute Demand.applicabilityCoordinate
applicabilityRoute = producerRoute Cross.legalTypedMeetProducer legalMeetPopulatesApplicability
  "typed legal applicability meet"

------------------------------------------------------------------------
-- Exact least-routing boundaries.
------------------------------------------------------------------------

data ReuseExistingRequiresProducerInvocation : Set where
data ParserCanPopulateLegalApplicability : Set where
data AttributionProducerCanResolveAuthority : Set where
data DocumentContextIsParserShape : Set where

actionReuseNeedsNoProducer :
  invocationNeed Planner.reuseExisting ≡ noProducerInvocation
actionReuseNeedsNoProducer = refl

missingEvidenceNeedsProducer :
  invocationNeed Planner.acquireMissingEvidence ≡ producerInvocationRequired
missingEvidenceNeedsProducer = refl

reuseHasLiteralNoProducerRoute :
  ∀ {coordinate} → WorkRoute noProducerInvocation coordinate
reuseHasLiteralNoProducerRoute = reuseWithoutProducer

reuseDoesNotInvokeProducer : ReuseExistingRequiresProducerInvocation → ⊥
reuseDoesNotInvokeProducer ()

parserDoesNotOwnLegalApplicability : ParserCanPopulateLegalApplicability → ⊥
parserDoesNotOwnLegalApplicability ()

attributionDoesNotOwnAuthority : AttributionProducerCanResolveAuthority → ⊥
attributionDoesNotOwnAuthority ()

documentContextDoesNotCollapseToParserShape : DocumentContextIsParserShape → ⊥
documentContextDoesNotCollapseToParserShape ()

record RequirementProducerRoutingBoundary : Set where
  constructor requirement-producer-routing-boundary
  field
    producerRoutingIsCoordinateIndexed : Bool
    satisfiedRequirementNeedsProducerInvocation : Bool
    parserMayPopulateLegalApplicability : Bool
    attributionMayResolveAuthority : Bool
    documentContextHasDedicatedProducerClass : Bool

canonicalRequirementProducerRoutingBoundary : RequirementProducerRoutingBoundary
canonicalRequirementProducerRoutingBoundary =
  requirement-producer-routing-boundary true false false false true
