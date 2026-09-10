module DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Wikimedia.NativeConcreteQidGraphProjectionExact as Qid
import DASHI.Core.TechnicalDependencyHypergraphExact as Tech

------------------------------------------------------------------------
-- ABSTRACT WRONGTYPE / ERROR TRANSPORT SURFACE
--
-- Cross-pollination target:
--   SensibLaw WrongType
--   programming type/attribute errors
--   attribution/provenance errors
--   FactorsThrough / nonfactorability
--   fallacy obstruction
--   Ibrahim first-link / Snowball traversal
--   QID identity coordinates
--   project planning and dependency graphs.
--
-- WrongType here is deliberately abstract.  It means that an offered object
-- may be internally well-formed yet inhabit the wrong indexed obligation.
------------------------------------------------------------------------

data TransportObligationKind : Set where
  computationalTypeObligation : TransportObligationKind
  objectAttributeObligation : TransportObligationKind
  provenanceAttributionObligation : TransportObligationKind
  indexedWrongTypeObligation : TransportObligationKind
  admissibleTransitionObligation : TransportObligationKind
  consumerFactorisationObligation : TransportObligationKind
  inferencePromotionObligation : TransportObligationKind
  projectDependencyObligation : TransportObligationKind
  projectAssignmentObligation : TransportObligationKind
  projectMilestoneObligation : TransportObligationKind
  projectRiskObligation : TransportObligationKind
  projectAcceptanceObligation : TransportObligationKind

record IndexedObligation : Set where
  constructor indexed-obligation
  field
    obligationKind : TransportObligationKind
    obligationIndex : String
    consumerReference : String
    scopeReference : String
open IndexedObligation public

record OfferedCandidate : Set where
  constructor offered-candidate
  field
    candidateReference : String
    candidateClass : String
    provenanceReference : String
    wellFormed : Bool
open OfferedCandidate public

data AbstractWrongTypeMismatch : Set where
  wrongComputationalType : AbstractWrongTypeMismatch
  missingObjectAttribute : AbstractWrongTypeMismatch
  wrongAttribution : AbstractWrongTypeMismatch
  wrongIndexedObligation : AbstractWrongTypeMismatch
  inadmissibleCandidate : AbstractWrongTypeMismatch
  nonFactorableRepresentation : AbstractWrongTypeMismatch
  invalidInferenceTransport : AbstractWrongTypeMismatch
  wrongProjectDependency : AbstractWrongTypeMismatch
  wrongProjectAssignee : AbstractWrongTypeMismatch
  wrongProjectMilestone : AbstractWrongTypeMismatch
  wrongProjectRiskClassification : AbstractWrongTypeMismatch
  wrongProjectAcceptanceReceipt : AbstractWrongTypeMismatch

record WrongTypeErrorReceipt : Set where
  constructor wrong-type-error-receipt
  field
    expected : IndexedObligation
    offered : OfferedCandidate
    mismatch : AbstractWrongTypeMismatch
    rejectionReference : String
    rejectionDoesNotNegateCandidateExistence : Bool
open WrongTypeErrorReceipt public

------------------------------------------------------------------------
-- ATTRIBUTE != ATTRIBUTION.
------------------------------------------------------------------------

data AttributeAttributionDistinction : Set where
  structuralMemberLookup : AttributeAttributionDistinction
  provenanceAuthorityRelation : AttributeAttributionDistinction

data AttributeErrorEqualsAttributionError : Set where

attributeErrorDoesNotCollapseIntoAttributionError :
  AttributeErrorEqualsAttributionError → ⊥
attributeErrorDoesNotCollapseIntoAttributionError ()

------------------------------------------------------------------------
-- ATTRIBUTION ERROR IS ALSO AN INFERENCE FALLACY.
--
-- The inherited catalogue remains untouched; this is a thin extension that
-- names attribution-specific transport as its own fallacy rather than forcing
-- it into semantic equivocation or missing-receipt by fiat.
------------------------------------------------------------------------

data CrossDomainFallacy : Set where
  inheritedFallacy : Fallacy.FallacyObstruction → CrossDomainFallacy
  attributionFallacy : CrossDomainFallacy

record AttributionFallacyReceipt : Set where
  constructor attribution-fallacy-receipt
  field
    propositionReference : String
    assertedAttributionReference : String
    requiredProvenanceConsumer : String
    obstruction : CrossDomainFallacy
    obstructionIsAttributionFallacy : obstruction ≡ attributionFallacy
    propositionMayStillBeTrue : Bool
    attributionPromotesAuthority : Bool
    attributionPromotesAuthorityIsFalse : attributionPromotesAuthority ≡ false
open AttributionFallacyReceipt public

------------------------------------------------------------------------
-- FACTORS-THROUGH ADAPTER.
--
-- Adequacy is consumer-relative.  A representation can answer one query while
-- erasing provenance, assignment, dependency, risk, or acceptance distinctions
-- needed by another.
------------------------------------------------------------------------

ConsumerAdequate :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) →
  (State → Outcome) →
  Set
ConsumerAdequate = INF.FactorsThrough

record FactorisationDemand {State Surface Outcome : Set} : Set₁ where
  constructor factorisation-demand
  field
    representation : State → Surface
    consumer : State → Outcome
    demandReference : String
open FactorisationDemand public

record FactorisationErrorReceipt {State Surface Outcome : Set}
    (demand : FactorisationDemand {State} {Surface} {Outcome}) : Set₁ where
  constructor factorisation-error-receipt
  field
    leftState : State
    rightState : State
    sameRepresentation : representation demand leftState ≡ representation demand rightState
    consumerDistinguishes : consumer demand leftState ≡ consumer demand rightState → ⊥
    errorReference : String
open FactorisationErrorReceipt public

factorisationWitnessRulesOutAdequacy :
  ∀ {State Surface Outcome : Set}
    {demand : FactorisationDemand {State} {Surface} {Outcome}} →
  FactorisationErrorReceipt demand →
  ConsumerAdequate (representation demand) (consumer demand) →
  ⊥
factorisationWitnessRulesOutAdequacy receipt factors =
  consumerDistinguishes receipt
    (INF.factorisation factors (leftState receipt) (rightState receipt)
      (sameRepresentation receipt))

------------------------------------------------------------------------
-- SNOWBALL / IBRAHIM / QID / TECHNICAL GRAPH COORDINATE.
--
-- QID is identity metadata, not proof.  Ibrahim traversal is discovery and
-- explanatory-parent projection, not theorem implication.  Technical edges
-- carry source-typed dependency semantics.  Project planning consumes the same
-- graph under planning-specific queries.
------------------------------------------------------------------------

record ErrorSnowballNode : Set where
  constructor error-snowball-node
  field
    knowledgeCoordinate : Ibrahim.DashiKnowledgeCoordinate
    planningRole : String
    errorFamilyReference : String
    qidCoordinateOnly : Bool
    formulationOwnerRetained : Bool
open ErrorSnowballNode public

data PlanningEdgeKind : Set where
  planDependsOn : PlanningEdgeKind
  planBlocks : PlanningEdgeKind
  planAssignedTo : PlanningEdgeKind
  planMilestoneFor : PlanningEdgeKind
  planRiskOf : PlanningEdgeKind
  planAcceptedBy : PlanningEdgeKind
  planSupportedBy : PlanningEdgeKind
  planCrossPollinatesWith : PlanningEdgeKind

record PlanningSnowballEdge : Set where
  constructor planning-snowball-edge
  field
    fromNode : ErrorSnowballNode
    toNode : ErrorSnowballNode
    edgeKind : PlanningEdgeKind
    ibrahimEdge : Ibrahim.DashiFirstLinkEdge
    technicalReceipt : Tech.TechnicalHyperedge
    edgeReference : String
open PlanningSnowballEdge public

record QidProjectionBoundaryWitness : Set where
  constructor qid-projection-boundary-witness
  field
    qidProjectionBoundary : Qid.NativeConcreteProjectionBoundary
    qidIdentityIsProof : Bool
    qidIdentityIsProofIsFalse : qidIdentityIsProof ≡ false
    arbitraryNativePropertyIsPlanningDependency : Bool
    arbitraryNativePropertyIsPlanningDependencyIsFalse :
      arbitraryNativePropertyIsPlanningDependency ≡ false
open QidProjectionBoundaryWitness public

canonicalQidProjectionBoundaryWitness : QidProjectionBoundaryWitness
canonicalQidProjectionBoundaryWitness =
  qid-projection-boundary-witness
    Qid.canonicalNativeConcreteProjectionBoundary
    false refl
    false refl

------------------------------------------------------------------------
-- PROJECT PLANNING AS CONSUMER FAMILY.
------------------------------------------------------------------------

data ProjectPlanningQuery : Set where
  dependencyQuery : ProjectPlanningQuery
  assignmentQuery : ProjectPlanningQuery
  milestoneQuery : ProjectPlanningQuery
  riskQuery : ProjectPlanningQuery
  acceptanceQuery : ProjectPlanningQuery
  provenanceQuery : ProjectPlanningQuery

data ProjectPlanningAnswer : Set where
  planningAnswer : String → ProjectPlanningAnswer

record ProjectPlanningConsumerFamily (State Surface : Set) : Set₁ where
  constructor project-planning-consumer-family
  field
    projectSurface : State → Surface
    answer : ProjectPlanningQuery → State → ProjectPlanningAnswer
    dependencyFactors : ConsumerAdequate projectSurface (answer dependencyQuery)
    assignmentFactors : ConsumerAdequate projectSurface (answer assignmentQuery)
    milestoneFactors : ConsumerAdequate projectSurface (answer milestoneQuery)
    riskFactors : ConsumerAdequate projectSurface (answer riskQuery)
    acceptanceFactors : ConsumerAdequate projectSurface (answer acceptanceQuery)
    provenanceFactors : ConsumerAdequate projectSurface (answer provenanceQuery)
open ProjectPlanningConsumerFamily public

------------------------------------------------------------------------
-- NON-COLLAPSE REGRESSIONS.
------------------------------------------------------------------------

data WellTypedImpliesAdmissible : Set where
data QidImpliesAttribution : Set where
data SameLabelImpliesSameWrongType : Set where
data CorrectContentImpliesCorrectAttribution : Set where
data FallacyImpliesFalseConclusion : Set where
data PlanningAdjacencyImpliesDependency : Set where
data DependencyImpliesAssignment : Set where
data MilestoneImpliesAcceptance : Set where

wellTypedDoesNotAutomaticallyMeanAdmissible : WellTypedImpliesAdmissible → ⊥
wellTypedDoesNotAutomaticallyMeanAdmissible ()

qidDoesNotManufactureAttribution : QidImpliesAttribution → ⊥
qidDoesNotManufactureAttribution ()

sameLabelDoesNotIdentifyWrongType : SameLabelImpliesSameWrongType → ⊥
sameLabelDoesNotIdentifyWrongType ()

correctContentDoesNotManufactureAttribution : CorrectContentImpliesCorrectAttribution → ⊥
correctContentDoesNotManufactureAttribution ()

fallacyDoesNotNegateConclusion : FallacyImpliesFalseConclusion → ⊥
fallacyDoesNotNegateConclusion ()

planningAdjacencyDoesNotCreateDependency : PlanningAdjacencyImpliesDependency → ⊥
planningAdjacencyDoesNotCreateDependency ()

dependencyDoesNotAssignActor : DependencyImpliesAssignment → ⊥
dependencyDoesNotAssignActor ()

milestoneDoesNotCreateAcceptance : MilestoneImpliesAcceptance → ⊥
milestoneDoesNotCreateAcceptance ()

record CrossPollinationBoundary : Set where
  constructor cross-pollination-boundary
  field
    wrongTypeIsAbstractIndexedMismatch : Bool
    attributionIsDistinctFromAttribute : Bool
    attributionIsFallacySector : Bool
    factorsThroughDefinesConsumerAdequacy : Bool
    qidIsIdentityCoordinateOnly : Bool
    ibrahimTraversalCreatesProof : Bool
    projectPlanningUsesSameDependencyGraph : Bool
    planningAdjacencyCreatesDependency : Bool
open CrossPollinationBoundary public

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  cross-pollination-boundary
    true true true true true false true false
