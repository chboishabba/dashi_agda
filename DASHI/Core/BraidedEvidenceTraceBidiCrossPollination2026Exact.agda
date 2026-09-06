module DASHI.Core.BraidedEvidenceTraceBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Textile

------------------------------------------------------------------------
-- BRAIDED EVIDENCE TRACE -- BIDI CROSS-POLLINATION
--
-- DASHI extension, not a theorem attributed to the motivating sources.
--
-- Source calibration:
-- Bartlett, Cheryl; Marshall, Murdena; Marshall, Albert (2012),
-- "Two-Eyed Seeing and other lessons learned within a co-learning journey of
-- bringing together indigenous and mainstream knowledges and ways of knowing",
-- Journal of Environmental Studies and Sciences 2:331-340,
-- DOI 10.1007/s13412-012-0086-8.
--
-- Textile donor authority is repository-owned:
-- DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact.
--
-- Bounded reading: distinct strands may be coordinated without being fused;
-- provenance/authority/permission/obligation remain strand-local unless an
-- explicit crossing receipt transports something between them.
------------------------------------------------------------------------

data StrandRole : Set where
  provenanceWarp authorityWarp permissionWarp obligationWarp observationWeft proofWeft : StrandRole

data CrossingKind : Set where
  coexistenceCrossing translationCrossing comparisonCrossing corroborationCrossing : CrossingKind

record EvidenceStrand : Set where
  constructor evidence-strand
  field
    strandID : String
    role : StrandRole
    sourceReference : String
    authorityReference : String

open EvidenceStrand public

record BraidedCrossing (left right : EvidenceStrand) : Set where
  constructor braided-crossing
  field
    kind : CrossingKind
    compatibilityReceipt : String
    translationReceipt : String
    leftIdentityRetained : Bool
    leftIdentityRetainedIsTrue : leftIdentityRetained ≡ true
    rightIdentityRetained : Bool
    rightIdentityRetainedIsTrue : rightIdentityRetained ≡ true

open BraidedCrossing public

record BraidedEvidenceTrace : Set where
  constructor braided-evidence-trace
  field
    strands : List EvidenceStrand
    traceReference : String
    noAutomaticFusion : Bool
    noAutomaticFusionIsTrue : noAutomaticFusion ≡ true

open BraidedEvidenceTrace public

------------------------------------------------------------------------
-- Direct donor adapters: the cross-pollination carries the original objects,
-- rather than replacing them with detached summaries.
------------------------------------------------------------------------

record KnowledgeStrand : Set where
  constructor knowledge-strand
  field
    carrier : IK.KnowledgeCarrier
    provenanceReference : String

open KnowledgeStrand public

record TextileProofStrand : Set₁ where
  constructor textile-proof-strand
  field
    FabricCarrier : Set
    fabricReference : String
    donorModuleReference : String

open TextileProofStrand public

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data CrossingFusesStrands : Set where

data SharedContentTransfersAuthority : Set where

data SharedContentTransfersPermission : Set where

data MaterialTraceCreatesProofAuthority : Set where

crossingDoesNotFuseStrands : CrossingFusesStrands → ⊥
crossingDoesNotFuseStrands ()

sharedContentDoesNotTransferAuthority : SharedContentTransfersAuthority → ⊥
sharedContentDoesNotTransferAuthority ()

sharedContentDoesNotTransferPermission : SharedContentTransfersPermission → ⊥
sharedContentDoesNotTransferPermission ()

materialTraceDoesNotCreateProofAuthority : MaterialTraceCreatesProofAuthority → ⊥
materialTraceDoesNotCreateProofAuthority ()

record BraidedEvidenceBoundary : Set where
  constructor braided-evidence-boundary
  field
    coordinationWithoutFusion : Bool
    crossingRequiresReceipt : Bool
    provenanceRemainsStrandLocal : Bool
    authorityRemainsStrandLocal : Bool
    permissionRemainsStrandLocal : Bool

canonicalBraidedEvidenceBoundary : BraidedEvidenceBoundary
canonicalBraidedEvidenceBoundary =
  braided-evidence-boundary true true true true true
