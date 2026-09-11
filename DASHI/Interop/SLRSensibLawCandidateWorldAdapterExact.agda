module DASHI.Interop.SLRSensibLawCandidateWorldAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawBroadcastDiscourseSpanReconstructionExact as Spans
import DASHI.Cognition.PNF.SensibLawDiscourseQualityAuditExact as Quality
import DASHI.Cognition.PNF.SensibLawRoleTransitionManifoldExact as Roles
import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as Roadmap

------------------------------------------------------------------------
-- SLR -> SensibLaw CandidateWorldModel adapter.
--
-- Runtime target:
--   SensibLaw/src/policy/world_model.py::sl.candidate_world_model.v0_1
--
-- The point is schema reuse, not another world-model ontology.  Existing SLR
-- TSV rows are projected into the generic candidate carrier while retaining
-- ambiguity, typed-role debt, source provenance, and candidate-only status.
------------------------------------------------------------------------

data SLRTable : Set where
  discourseSpansV4 : SLRTable
  discourseQualityV1 : SLRTable
  roleTransitionsV1 : SLRTable


data CandidateWorldCollection : Set where
  claimsCollection : CandidateWorldCollection
  relationsCollection : CandidateWorldCollection
  conflictsCollection : CandidateWorldCollection
  residualsCollection : CandidateWorldCollection
  provenanceCollection : CandidateWorldCollection
  entitiesCollection : CandidateWorldCollection
  eventsCollection : CandidateWorldCollection
  timelinesCollection : CandidateWorldCollection
  authoritySurfacesCollection : CandidateWorldCollection
  externalPressureCollection : CandidateWorldCollection


record TableProjection : Set where
  constructor tableProjection
  field
    sourceTable : SLRTable
    sourceColumn : String
    targetCollection : CandidateWorldCollection
    targetField : String
    exactSemanticCarry : Bool
    requiresLaterConsumer : Bool
    note : String

open TableProjection public

canonicalTableProjection : List TableProjection
canonicalTableProjection =
    tableProjection discourseSpansV4 "span_id"
      claimsCollection "node_id" true false
      "A reconstructed span is carried as a candidate discourse-span node."
  ∷ tableProjection discourseSpansV4 "boundary_projection"
      relationsCollection "relation_kind" true false
      "Adjacent reconstructed spans carry the admitted boundary projection as a candidate relation."
  ∷ tableProjection discourseSpansV4 "char_start,char_end"
      claimsCollection "metadata" true false
      "Source offsets remain metadata; adapter does not re-tokenise or rewrite source text."
  ∷ tableProjection discourseQualityV1 "node_id"
      claimsCollection "node_id" true false
      "Each rank-one discourse boundary remains an independently addressable candidate node."
  ∷ tableProjection discourseQualityV1 "pareto_fibres,pareto_width,pnf_residual_count"
      residualsCollection "residual" true false
      "Pareto multiplicity and PNF debt remain residual coordinates rather than scalar truth scores."
  ∷ tableProjection discourseQualityV1 "projection=unresolved"
      conflictsCollection "conflict_id,alternatives" true false
      "Unresolved Pareto fronts are represented as conflicts, not silently collapsed."
  ∷ tableProjection discourseQualityV1 "hidden_speaker_splice_risk,false_cut_risk"
      residualsCollection "risk_flags" true false
      "Diagnostic risks remain candidate residuals and do not verify a speaker boundary."
  ∷ tableProjection roleTransitionsV1 "crossing_roles"
      claimsCollection "metadata" true false
      "Actor/patient/clause/coordination/predicate-aux observations remain typed boundary metadata."
  ∷ tableProjection roleTransitionsV1 "actor_crossing,patient_crossing,clause_crossing,predicate_aux_crossing"
      residualsCollection "typed_role_constraints" true false
      "Role compatibility is preserved for downstream world constraints and review."
  ∷ tableProjection discourseQualityV1 "world_mismatch_observed=not-observed"
      externalPressureCollection "external_pressure_results" false true
      "No pressure row is emitted until a separate world-constraint receipt exists."
  ∷ []

------------------------------------------------------------------------
-- Runtime output contract.
------------------------------------------------------------------------

record SLRSensibLawWorldAdapterReceipt : Set where
  constructor slrSensibLawWorldAdapterReceipt
  field
    runtimeSchemaReference : String
    targetSchemaReference : String
    modelStatusReference : String
    laneFamilyReference : String
    spanNodesReference : String
    boundaryNodesReference : String
    adjacencyRelationsReference : String
    conflictsReference : String
    residualsReference : String
    provenanceReference : String
    worldConstraintStatusReference : String
    candidateOnly : Bool
    semanticPromotion : Bool
    reTokenisesSource : Bool
    rewritesSourceOffsets : Bool
    createsAuthoritySurface : Bool

open SLRSensibLawWorldAdapterReceipt public

canonicalSLRSensibLawWorldAdapterReceipt : SLRSensibLawWorldAdapterReceipt
canonicalSLRSensibLawWorldAdapterReceipt =
  slrSensibLawWorldAdapterReceipt
    "slr-sensiblaw-world-adapter-v1"
    "sl.candidate_world_model.v0_1"
    "candidate"
    "slr_discourse"
    "claims[node_kind=discourse_span_candidate]"
    "claims[node_kind=discourse_boundary_candidate]"
    "relations[relation_kind=discourse_boundary:*]"
    "conflicts[conflict_kind=discourse_pareto_multiplicity]"
    "residuals[typed discourse/role/PNF debt]"
    "provenance_graph[source sha256 -> candidate node]"
    "not_attached"
    true false false false false

------------------------------------------------------------------------
-- Cross-compatibility status.
------------------------------------------------------------------------

data CompatibilityStatus : Set where
  exactCarrierMatch : CompatibilityStatus
  exactFieldSemantics : CompatibilityStatus
  conservativeProjection : CompatibilityStatus
  pendingWorldConstraint : CompatibilityStatus
  pendingDomainSemanticPromotion : CompatibilityStatus

record SLRTableCompatibility : Set where
  constructor slrTableCompatibility
  field
    spanCarrier : CompatibilityStatus
    boundaryCarrier : CompatibilityStatus
    relationCarrier : CompatibilityStatus
    residualCarrier : CompatibilityStatus
    conflictCarrier : CompatibilityStatus
    provenanceCarrier : CompatibilityStatus
    worldConstraintCarrier : CompatibilityStatus
    domainEntityCarrier : CompatibilityStatus
    note : String

open SLRTableCompatibility public

canonicalSLRTableCompatibility : SLRTableCompatibility
canonicalSLRTableCompatibility =
  slrTableCompatibility
    conservativeProjection
    conservativeProjection
    conservativeProjection
    exactFieldSemantics
    exactFieldSemantics
    exactFieldSemantics
    pendingWorldConstraint
    pendingDomainSemanticPromotion
    "SLR tables already fit the generic CandidateWorldModel carrier; domain entities/events and world pressure remain separate later-consumer obligations."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TableCompatibilityMeansSemanticIdentity : Set where
data BoundaryCandidateMeansWorldClaim : Set where
data UnresolvedProjectionMayBeDropped : Set where
data RiskFlagVerifiesSpeakerBoundary : Set where
data MissingWorldReceiptMayCreatePressure : Set where
data AdapterMayPromoteTruth : Set where
data AdapterMayRetokeniseSource : Set where

tableCompatibilityDoesNotMeanSemanticIdentity :
  TableCompatibilityMeansSemanticIdentity → ⊥
tableCompatibilityDoesNotMeanSemanticIdentity ()

boundaryCandidateDoesNotMeanWorldClaim : BoundaryCandidateMeansWorldClaim → ⊥
boundaryCandidateDoesNotMeanWorldClaim ()

unresolvedProjectionMayNotBeDropped : UnresolvedProjectionMayBeDropped → ⊥
unresolvedProjectionMayNotBeDropped ()

riskFlagDoesNotVerifySpeakerBoundary : RiskFlagVerifiesSpeakerBoundary → ⊥
riskFlagDoesNotVerifySpeakerBoundary ()

missingWorldReceiptDoesNotCreatePressure : MissingWorldReceiptMayCreatePressure → ⊥
missingWorldReceiptDoesNotCreatePressure ()

adapterDoesNotPromoteTruth : AdapterMayPromoteTruth → ⊥
adapterDoesNotPromoteTruth ()

adapterDoesNotRetokeniseSource : AdapterMayRetokeniseSource → ⊥
adapterDoesNotRetokeniseSource ()

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

spanBoundaryAnchor : Spans.SpanReconstructionBoundary
spanBoundaryAnchor = Spans.canonicalSpanReconstructionBoundary

qualityBoundaryAnchor : Quality.DiscourseQualityBoundary
qualityBoundaryAnchor = Quality.canonicalDiscourseQualityBoundary

roleBoundaryAnchor : Roles.RoleTransitionBoundary
roleBoundaryAnchor = Roles.canonicalRoleTransitionBoundary

roadmapBoundaryAnchor : Roadmap.SuiteConvergenceLaw
roadmapBoundaryAnchor = Roadmap.canonicalSuiteConvergenceLaw
