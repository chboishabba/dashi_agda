module DASHI.Policy.ABC730DiscourseRepairOverlayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Transcript
import DASHI.Cognition.PNF.SensibLawBroadcastDiscourseSpanReconstructionExact as Spans
import DASHI.Cognition.PNF.SensibLawRoleTransitionManifoldExact as Roles

------------------------------------------------------------------------
-- Discourse repair overlay for the canonical ABC 7.30 transcript claim ledger.
--
-- The 81 TranscriptClaim values remain source-native authority.  This module
-- attaches reconstruction/discourse receipts to existing claim IDs without
-- rewriting propositions, source spans, claim classes, or speaker identities.
------------------------------------------------------------------------

data RepairDisposition : Set where
  sourceSpanStable : RepairDisposition
  discourseStructureRefined : RepairDisposition
  attributionStillUnresolved : RepairDisposition
  nestedAttributionPreserved : RepairDisposition
  incidentalSpeechExcluded : RepairDisposition
  downstreamReviewRequired : RepairDisposition

record ClaimDiscourseRepair : Set where
  constructor claimDiscourseRepair
  field
    claimReference : String
    canonicalClaimReference : String
    reconstructionReceiptReference : String
    discourseQualityReceiptReference : String
    roleTransitionReceiptReference : String
    disposition : RepairDisposition
    speakerIdentityPromoted : Bool
    propositionRewritten : Bool
    sourceSpanRewritten : Bool
    residualReference : String

open ClaimDiscourseRepair public

------------------------------------------------------------------------
-- First repair frontier.
------------------------------------------------------------------------

c030Repair : ClaimDiscourseRepair
c030Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C030"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c030"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  attributionStillUnresolved
  false false false
  "speaker candidate/discourse boundary may be refined, but the supplied transcript does not independently verify the named speaker"

c031Repair : ClaimDiscourseRepair
c031Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C031"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c031"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  attributionStillUnresolved
  false false false
  "retain speakerUnresolved until an independent labelled speaker receipt pays identity"

c032Repair : ClaimDiscourseRepair
c032Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C032"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c032"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  attributionStillUnresolved
  false false false
  "the exact gaslighting wording remains transcript-supported; discourse reconstruction does not by itself establish Bandt or Shoebridge as speaker"

c033Repair : ClaimDiscourseRepair
c033Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C033"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c033"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  attributionStillUnresolved
  false false false
  "government-defending voice remains source-level unresolved even if a candidate discourse boundary is reconstructed"

c049Repair : ClaimDiscourseRepair
c049Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C049"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c049"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  nestedAttributionPreserved
  false false false
  "question/interview content remains nested attribution rather than a promoted proposition"

c080Repair : ClaimDiscourseRepair
c080Repair = claimDiscourseRepair
  "ABC730-2026-09-09-C080"
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.c080"
  "slr-discourse-spans-v4"
  "slr-discourse-quality-v1"
  "slr-role-transition-v1"
  incidentalSpeechExcluded
  false false false
  "incidental recording speech remains outside the sanctions-policy claim surface"

repairFrontier : List ClaimDiscourseRepair
repairFrontier = c030Repair ∷ c031Repair ∷ c032Repair ∷ c033Repair ∷ c049Repair ∷ c080Repair ∷ []

------------------------------------------------------------------------
-- Canonical high-value policy claims remain stable while discourse attribution
-- is repaired separately.
------------------------------------------------------------------------

canonicalUKImportBan : Transcript.TranscriptClaim
canonicalUKImportBan = Transcript.abcUKImportBanClaim

canonicalAustraliaNoBlanketBan : Transcript.TranscriptClaim
canonicalAustraliaNoBlanketBan = Transcript.abcAustraliaNoBlanketBanClaim

canonicalAustraliaRationale : Transcript.TranscriptClaim
canonicalAustraliaRationale = Transcript.abcAustraliaUnintendedConsequencesRationale

canonicalGaslightingWords : Transcript.TranscriptClaim
canonicalGaslightingWords = Transcript.abcLaborGaslightingClaim

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DiscourseRepairRewritesCanonicalClaim : Set where
discourseRepairDoesNotRewriteCanonicalClaim : DiscourseRepairRewritesCanonicalClaim → ⊥
discourseRepairDoesNotRewriteCanonicalClaim ()

data ReconstructedBoundaryVerifiesSpeaker : Set where
reconstructedBoundaryDoesNotVerifySpeaker : ReconstructedBoundaryVerifiesSpeaker → ⊥
reconstructedBoundaryDoesNotVerifySpeaker ()

data LowerResidualPromotesPolicyTruth : Set where
lowerResidualDoesNotPromotePolicyTruth : LowerResidualPromotesPolicyTruth → ⊥
lowerResidualDoesNotPromotePolicyTruth ()

data AttributionRepairPromotesEvaluativeTruth : Set where
attributionRepairDoesNotPromoteEvaluativeTruth : AttributionRepairPromotesEvaluativeTruth → ⊥
attributionRepairDoesNotPromoteEvaluativeTruth ()

data DiscourseQualityMetricCreatesWorldMismatchFact : Set where
discourseQualityMetricDoesNotCreateWorldMismatchFact : DiscourseQualityMetricCreatesWorldMismatchFact → ⊥
discourseQualityMetricDoesNotCreateWorldMismatchFact ()

record ABC730DiscourseRepairBoundary : Set where
  constructor abc730DiscourseRepairBoundary
  field
    canonicalClaimsRemainAuthoritative : Bool
    overlayMayRefineDiscourseStructure : Bool
    overlayMayRewritePropositions : Bool
    reconstructedBoundaryMayVerifySpeaker : Bool
    nestedAttributionRemainsNested : Bool
    policyClaimsRemainIndependentOfSpeakerRepair : Bool
    worldMismatchRequiresSeparateReceipt : Bool

canonicalABC730DiscourseRepairBoundary : ABC730DiscourseRepairBoundary
canonicalABC730DiscourseRepairBoundary =
  abc730DiscourseRepairBoundary true true false false true true true

spanBoundaryAnchor : Spans.SpanReconstructionBoundary
spanBoundaryAnchor = Spans.canonicalSpanReconstructionBoundary

roleBoundaryAnchor : Roles.RoleTransitionBoundary
roleBoundaryAnchor = Roles.canonicalRoleTransitionBoundary
