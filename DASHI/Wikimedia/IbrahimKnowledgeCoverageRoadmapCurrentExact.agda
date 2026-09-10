module DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapCurrentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Historical
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapDeltaExact as Delta
import DASHI.Wikimedia.IbrahimSnowballMemoryRepetitionSourceDependencyConsensusBidiExact as Dependency
import DASHI.Wikimedia.IbrahimSnowballEvidenceSynthesisPeerReviewConflictIndependenceBidiExact as Synthesis
import DASHI.Wikimedia.IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact as NDim
import DASHI.Wikimedia.IbrahimSnowballAtomicClaimIntentExperimentAdequacyBidiExact as Atomic
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey

------------------------------------------------------------------------
-- LIVE IBRAHIM ROADMAP
--
-- Historical owns the original rank-1..10 discovery roadmap.
-- Delta records later payment/narrowing.
-- This owner records the current frontier after the newest dependency,
-- evidence-synthesis, N-dimensional proof-search and atomic-claim tranches.
-- It is intentionally a thin status/navigation surface.
------------------------------------------------------------------------

data LiveState : Set where
  completeAsParent : LiveState
  residualOnly : LiveState
  concreteConsumerNeeded : LiveState
  compositionNeeded : LiveState

record LiveRoadmapTarget : Set where
  constructor live-roadmap-target
  field
    rank : Nat
    target : String
    state : LiveState
    alreadyPaidBy : String
    remaining : String
    qidCoordinate : String
    deweyCoordinate : String
    sourceCoordinate : String
    completionTest : String
open LiveRoadmapTarget public

------------------------------------------------------------------------
-- The prior independence/consensus frontier was paid concurrently.
------------------------------------------------------------------------

independenceConsensusNowPaid : LiveRoadmapTarget
independenceConsensusNowPaid = live-roadmap-target
  0
  "Corroboration / replication / common-source dependence / evidence synthesis / peer review / consensus"
  completeAsParent
  "LearningMemoryTraumaReplicationConsensus; MemoryRepetitionSourceDependencyConsensus; EvidenceSynthesisPeerReviewConflictIndependence"
  "only consumer-specific source-dependency calculations remain"
  "reproducibility Q1425625; scientific consensus Q316748; systematic review Q1504425; peer review Q215028; conflict of interest Q211067"
  "unresolved where no exact inspected DDC is paid"
  "DOI-bounded independence/evidence-synthesis sources travel with local owners"
  "future work must exhibit a concrete dependence structure not representable by the shared provenance grammar"

atomicExperimentAdequacyNowPaid : LiveRoadmapTarget
atomicExperimentAdequacyNowPaid = live-roadmap-target
  0
  "Human intent / atomic claim / operationalization / experiment / exact consumer"
  completeAsParent
  "DependencyNDimLocalGlobalProofSearch; AtomicClaimIntentExperimentAdequacy"
  "only domain-specific specification mismatches remain"
  "scientific hypothesis Q3144351; scientific method Q46857; operationalization Q286017"
  "no forced DDC for construct validity/operationalization"
  "Blackwell 1953 DOI 10.1214/aoms/1177729032; Cronbach-Meehl 1955 DOI 10.1037/h0040957"
  "green tests cannot be promoted unless constructor, operationalization and tested consumer match the intended atomic claim"

------------------------------------------------------------------------
-- Re-ranked live frontier.
------------------------------------------------------------------------

ethnographyParticipantObservation : LiveRoadmapTarget
ethnographyParticipantObservation = live-roadmap-target
  1
  "Ethnography / participant observation"
  compositionNeeded
  "Two-Eyed/community observer machinery; Brown observer plurality; social-influence consent/coercion; archive/source criticism; testimony/credibility"
  "compose one canonical fieldwork receipt retaining observer relation, participant role, consent/authority, time, interpretation, source provenance, affected-subject voice and revision"
  "ethnography Q132151; participant observation Q1129049"
  "DDC unresolved until an exact inspected classification is paid"
  "method/source citations should remain distinct from community testimony and institutional records"
  "one thin receipt composes existing primitives and proves observation/participation cannot manufacture consent, community authority or whole-system truth"

geologyBreadth : LiveRoadmapTarget
geologyBreadth = live-roadmap-target
  2
  "First concrete geology breadth consumer"
  concreteConsumerNeeded
  "Geology/Environment/DeepTimeCarbon plus archaeology and Tiwi ecological joins"
  "identify a downstream claim requiring stratigraphy, sedimentology, tectonics, geomorphology, petrology or geophysics that current owners cannot express"
  "geology Q1069; Earth science Q8008"
  "geology Q1069 carries inspected DDC 550 and 551; retain both rather than manufacture one semantic parent"
  "attach process/method DOI or primary survey only for the selected consumer"
  "a real downstream consumer reveals the missing geological coordinate before any taxonomy expansion"

healthcareBreadth : LiveRoadmapTarget
healthcareBreadth = live-roadmap-target
  3
  "First concrete healthcare/public-health consumer"
  concreteConsumerNeeded
  "Healthcare equality/access/governance owners"
  "separate clinical efficacy, public health, health services, access, institutional governance and individual evidence only when demanded by a real consumer"
  "health care Q31207; public health Q189603"
  "medical/library classification remains navigation only; no DDC promoted here without exact inspection"
  "medical efficacy requires domain-appropriate evidence; governance/access source cannot pay efficacy"
  "find one real existing DASHI consumer currently blocked by a healthcare-specific evidence distinction"

petrochemistryParentAudit : LiveRoadmapTarget
petrochemistryParentAudit = live-roadmap-target
  4
  "Petrochemistry / petroleum / refining / materials / emissions parent audit"
  residualOnly
  "SaltPetroleumIndustrialChemistryNetwork; IndustrialChemistryLogistics; DeepTimeCarbonBiosphereFossilFuel; climate branches"
  "determine whether duplicated feedstock/refining/material/emission edges still need one parent adapter"
  "petrochemistry Q493630"
  "Dewey unresolved in this owner; chemistry/engineering shelf choice is not semantic authority"
  "process-specific chemistry/engineering sources stay separate from climate/economic attribution"
  "add a parent only if a concrete duplicated transport survives quotienting"

------------------------------------------------------------------------
-- Cross-cutting roadmap completion criterion.
------------------------------------------------------------------------

record RoadmapCompletionCriterion : Set where
  constructor roadmap-completion-criterion
  field
    parentJointsRepresented : Bool
    qidAcquisitionPolicyPresent : Bool
    deweyIsNavigationOnly : Bool
    doiSourceRoleIsIndependentCoordinate : Bool
    provenanceIndependenceRepresented : Bool
    consumerAdequacyRepresented : Bool
    remainingBreadthIsConsumerDriven : Bool
    roadmapMeansEveryPossibleTopicFormalised : Bool
open RoadmapCompletionCriterion public

currentRoadmapCriterion : RoadmapCompletionCriterion
currentRoadmapCriterion = roadmap-completion-criterion
  true true true true true true true false

roadmapMeaning : String
roadmapMeaning =
  "roadmap completion means the shared navigation/provenance/consumer grammar can route new concrete demands to an existing owner or expose one typed residual; it does not mean pre-enumerating every Dewey subject, QID, DOI, discipline or empirical claim."

historicalPolicy : Historical.RoadmapPolicy
historicalPolicy = Historical.canonicalRoadmapPolicy

deltaPolicy : Delta.RoadmapDeltaPolicy
deltaPolicy = Delta.canonicalRoadmapDeltaPolicy

independenceBoundary : Synthesis.EvidenceSynthesisPeerReviewIndependenceBoundary
independenceBoundary = Synthesis.canonicalEvidenceSynthesisPeerReviewIndependenceBoundary

atomicBoundary : Atomic.AtomicClaimIntentExperimentAdequacyBoundary
atomicBoundary = Atomic.canonicalAtomicClaimIntentExperimentAdequacyBoundary
