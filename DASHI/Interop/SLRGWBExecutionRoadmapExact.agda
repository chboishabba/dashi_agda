module DASHI.Interop.SLRGWBExecutionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRGWBCandidateWorldProjectionExact as GWB

------------------------------------------------------------------------
-- GWB NEXT-RUN ROADMAP
--
-- GWB already has a strict ten-document SLR execution/parity certification.
-- The next run tests the common CandidateWorldModel ABI at corpus scale.  It
-- does not reuse transcript-only speaker/cut/path semantics.
------------------------------------------------------------------------

data GWBStageState : Set where
  paid : GWBStageState
  implementedAwaitingRuntime : GWBStageState
  next : GWBStageState
  notApplicableWithoutNewEvidence : GWBStageState

record GWBRoadmapCoordinate : Set where
  constructor gwbRoadmapCoordinate
  field
    stageReference : String
    state : GWBStageState
    paymentReference : String
    remainingResidualReference : String

open GWBRoadmapCoordinate public

gwbSLRRoadmap : List GWBRoadmapCoordinate
gwbSLRRoadmap =
  gwbRoadmapCoordinate
    "ten-document source projection + SLR direct/reference execution parity"
    paid
    "sensiblaw.gwb-full-certification-receipt.v0_1: 10 docs / 41,134 sentences / parity_failed=0 / published=false"
    "domain semantics are not paid by runtime parity"
  ∷ gwbRoadmapCoordinate
    "GWB certification -> SensibLaw CandidateWorldModel projection"
    implementedAwaitingRuntime
    "slr-gwb-candidate-world-v1 / SLRGWBCandidateWorldProjectionExact"
    "run text-free 41,134-sentence carrier projection and validate counts"
  ∷ gwbRoadmapCoordinate
    "SensibLaw normalization parity at GWB scale"
    next
    "normalize_world_model over sl.candidate_world_model.v0_1"
    "must preserve 41,134 sentence candidates, 41,124 structural adjacency relations and ten provenance records"
  ∷ gwbRoadmapCoordinate
    "claim-relative source-role atlas"
    next
    "official biographies / institutional biographies / secondary books / first-person memoir must remain distinct"
    "primaryness, DOI/QID/Dewey and authority remain claim-relative"
  ∷ gwbRoadmapCoordinate
    "canonical GWB claim/evidence projection"
    next
    "requires explicit claim fixtures or source-paid extraction receipts"
    "sentence identity and adjacency alone cannot manufacture canonical claims"
  ∷ gwbRoadmapCoordinate
    "broadcast speaker/path gold"
    notApplicableWithoutNewEvidence
    "GWB source set is biography/book prose, not a speaker-labelled broadcast transcript"
    "do not reuse ABC speaker-cut heuristics as if they were prose semantics"
  ∷ []

record GWBExecutionBoundary : Set where
  constructor gwbExecutionBoundary
  field
    transcriptSpecificDiscourseStackReusedBlindly : Bool
    certifiedSentenceCarrierReused : Bool
    sourceProjectionHashesReused : Bool
    rawBooksEmbeddedInWorldArtifact : Bool
    normalizationParityRequiredBeforeSemanticExpansion : Bool
    sourceRoleMayBeCollapsedAcrossAllDocuments : Bool
    canonicalClaimIdentityMayBeInferredFromAdjacency : Bool

open GWBExecutionBoundary public

canonicalGWBExecutionBoundary : GWBExecutionBoundary
canonicalGWBExecutionBoundary = gwbExecutionBoundary
  false true true false true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data GWBProseIsBroadcastTranscript : Set where
data CertifiedAdjacencyIsCanonicalClaimGraph : Set where
data FirstPersonMemoirIsPrimaryForAllEvents : Set where
data OfficialBiographyIsIndependentHistoricalProof : Set where
data SecondaryBookMayBePromotedBySLRParity : Set where

proseIsNotBroadcastTranscript : GWBProseIsBroadcastTranscript → ⊥
proseIsNotBroadcastTranscript ()

adjacencyIsNotCanonicalClaimGraph : CertifiedAdjacencyIsCanonicalClaimGraph → ⊥
adjacencyIsNotCanonicalClaimGraph ()

memoirIsNotPrimaryForAllEvents : FirstPersonMemoirIsPrimaryForAllEvents → ⊥
memoirIsNotPrimaryForAllEvents ()

officialBiographyIsNotIndependentProof : OfficialBiographyIsIndependentHistoricalProof → ⊥
officialBiographyIsNotIndependentProof ()

parityDoesNotPromoteSecondaryBook : SecondaryBookMayBePromotedBySLRParity → ⊥
parityDoesNotPromoteSecondaryBook ()

gwbProjectionAnchor : GWB.GWBCandidateWorldBoundary
gwbProjectionAnchor = GWB.canonicalGWBCandidateWorldBoundary
