module DASHI.Governance.PromotionSpineTests where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as Generic
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.ArtifactAuthorityPromotionBridge as AuthorityBridge
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.PromotionSpine as Spine

------------------------------------------------------------------------
-- Candidate-only rows cannot self-promote through the canonical gate.

exampleCandidateRow : Candidate.CandidateOnlyRow
exampleCandidateRow =
  Candidate.mkCandidateOnlyRow
    "example candidate"
    "DASHI.Governance.PromotionSpineTests"
    "exampleCandidateRow"
    Candidate.bridgeCandidateKind
    Candidate.bridgeCandidateOnlyStatus
    "candidate surface"
    "independent admissibility authority remains absent"

exampleCandidateReceipt :
  Candidate.CandidateOnlyReceipt exampleCandidateRow
exampleCandidateReceipt =
  Candidate.canonicalCandidateOnlyReceipt
    exampleCandidateRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

candidateExampleQuarantines :
  Canonical.promote
    (Spine.candidateOnlyObligations
      exampleCandidateReceipt
      true
      true
      true
      true)
    ≡ Canonical.quarantinedStatus
candidateExampleQuarantines =
  Spine.candidateOnlyQuarantines
    exampleCandidateReceipt
    true
    true
    true
    true

candidateExampleAbstains :
  Spine.authorizationFromObligations
    (Spine.candidateOnlyObligations
      exampleCandidateReceipt
      true
      true
      true
      true)
    ≡ Governed.abstain
candidateExampleAbstains =
  Spine.candidateOnlyAuthorizationAbstains
    exampleCandidateReceipt
    true
    true
    true
    true

------------------------------------------------------------------------
-- Generic receipt metadata adapts into an explicitly quarantined receipt.

exampleCodec : Canonical.Codec
exampleCodec =
  Canonical.mkCodec "raw" 85

exampleDigest : Canonical.Digest
exampleDigest =
  Canonical.mkDigest "sha2-256" "00"

exampleCID : Canonical.CID
exampleCID =
  Canonical.cidv1 1 exampleCodec exampleDigest

exampleGenericReceipt : Generic.GenericReceipt
exampleGenericReceipt =
  Generic.mkNonPromotingReceipt
    "example receipt"
    "DASHI.Governance.PromotionSpineTests"
    "exampleGenericReceipt"
    "metadata retained"
    "promotion remains external"
    "agda -i . DASHI/Governance/PromotionSpineTests.agda"

genericReceiptExampleQuarantined :
  Canonical.Receipt.status
    (Spine.genericReceiptToCanonical
      exampleGenericReceipt
      []
      []
      exampleCID)
    ≡ Canonical.quarantined
genericReceiptExampleQuarantined =
  Spine.genericReceiptRemainsQuarantined
    exampleGenericReceipt
    []
    []
    exampleCID

------------------------------------------------------------------------
-- Closed obligations select the candidate; candidate-only evidence preserves
-- the current canonical state.

exampleEnvelope :
  Governed.CandidateEnvelope Bool Bool Bool Bool
exampleEnvelope =
  Governed.candidateEnvelope
    false
    true
    true
    true
    false
    true

fullyClosedExampleOutcome :
  Governed.GovernedOutcome
    Bool Bool Bool Bool Bool Bool
    false
    true
fullyClosedExampleOutcome =
  Spine.governedOutcomeFromObligations
    exampleEnvelope
    (Canonical.promotionObligations true true true true true)
    Governed.pass
    []
    []
    false
    true

fullyClosedExampleSelectsCandidate :
  Governed.resultState fullyClosedExampleOutcome ≡ true
fullyClosedExampleSelectsCandidate =
  refl

candidateOnlyExampleOutcome :
  Governed.GovernedOutcome
    Bool Bool Bool Bool Bool Bool
    false
    true
candidateOnlyExampleOutcome =
  Spine.governedOutcomeFromObligations
    exampleEnvelope
    (Spine.candidateOnlyObligations
      exampleCandidateReceipt
      true
      true
      true
      true)
    Governed.warn
    []
    []
    false
    true

candidateOnlyExamplePreservesInput :
  Governed.resultState candidateOnlyExampleOutcome ≡ false
candidateOnlyExamplePreservesInput =
  Spine.candidateOnlyOutcomePreservesInput
    exampleCandidateReceipt
    exampleEnvelope
    true
    true
    true
    true
    Governed.warn
    []
    []
    false
    true

------------------------------------------------------------------------
-- Citation authority cannot masquerade as artifact authority.

exampleCitationBoundary :
  Authority.CitationAuthorityBoundary
exampleCitationBoundary =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "citation-example"
    "Example source"
    true
    false
    false
    []

exampleCitationOnlyEvidence :
  Authority.CitationAuthorityNoArtifact
exampleCitationOnlyEvidence =
  Authority.mkCitationAuthorityNoArtifact
    exampleCitationBoundary
    refl
    refl
    refl

citationExampleCannotCloseIdentity :
  AuthorityBridge.authorityIdentityClosed exampleCitationBoundary
    ≡ false
citationExampleCannotCloseIdentity =
  AuthorityBridge.citationOnlyCannotCloseArtifactIdentity
    exampleCitationOnlyEvidence

citationExampleQuarantines :
  Canonical.promote
    (AuthorityBridge.authorityPromotionObligations
      exampleCitationBoundary
      true
      true
      true
      true)
    ≡ Canonical.quarantinedStatus
citationExampleQuarantines =
  AuthorityBridge.citationOnlyQuarantines
    exampleCitationOnlyEvidence
    true
    true
    true
    true

------------------------------------------------------------------------
-- A real artifact boundary closes only the identity slot; the remaining four
-- canonical obligations must still be supplied independently.

exampleArtifactBoundary :
  Authority.ArtifactAuthorityBoundary
exampleArtifactBoundary =
  Authority.mkAuthorityBoundary
    Authority.ArtifactAuthority
    refl
    "artifact-example"
    "Example machine-readable artifact"
    true
    true
    true
    []

exampleArtifactClosure :
  AuthorityBridge.ArtifactAuthorityClosure exampleArtifactBoundary
exampleArtifactClosure =
  AuthorityBridge.artifactAuthorityClosure
    refl
    refl
    refl

artifactExamplePromotesWhenAllFiveClose :
  Canonical.promote
    (AuthorityBridge.authorityPromotionObligations
      exampleArtifactBoundary
      true
      true
      true
      true)
    ≡ Canonical.promoted
artifactExamplePromotesWhenAllFiveClose =
  AuthorityBridge.artifactAuthorityPromotesWhenRemainingClosed
    exampleArtifactClosure

artifactExampleAuthorizesGovernedPromotion :
  Spine.authorizationFromObligations
    (AuthorityBridge.authorityPromotionObligations
      exampleArtifactBoundary
      true
      true
      true
      true)
    ≡ Governed.promote
artifactExampleAuthorizesGovernedPromotion =
  AuthorityBridge.artifactAuthorityAuthorizesGovernedPromotion
    exampleArtifactClosure
