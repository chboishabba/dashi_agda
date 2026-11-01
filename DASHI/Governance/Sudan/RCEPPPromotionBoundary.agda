module DASHI.Governance.Sudan.RCEPPPromotionBoundary where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.ArtifactAuthorityPromotionBridge as ArtifactBridge
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Governance.Sudan.RCEPPSourceBoundary as Source

------------------------------------------------------------------------
-- RCEPP source-to-promotion boundary.
--
-- The supplied Charter closes a citation-identification slot only.  It does
-- not supply an authenticated machine-readable constitutional artifact, an
-- operative legal order, or a popular-recognition token.  Consequently even
-- optimistic downstream closure bits cannot authorize canonical promotion.
------------------------------------------------------------------------

rceppCitationIdentityRemainsOpen :
  ArtifactBridge.authorityIdentityClosed
    Source.canonicalRCEPPCitationBoundary
  ≡ false
rceppCitationIdentityRemainsOpen =
  ArtifactBridge.citationOnlyCannotCloseArtifactIdentity
    Source.canonicalRCEPPCitationHasNoArtifact

rceppCitationOnlyQuarantines :
  Canonical.promote
    (ArtifactBridge.authorityPromotionObligations
      Source.canonicalRCEPPCitationBoundary
      true
      true
      true
      true)
  ≡ Canonical.quarantinedStatus
rceppCitationOnlyQuarantines =
  ArtifactBridge.citationOnlyQuarantines
    Source.canonicalRCEPPCitationHasNoArtifact
    true
    true
    true
    true

rceppCitationOnlyAuthorizationAbstains :
  Promotion.authorizationFromObligations
    (ArtifactBridge.authorityPromotionObligations
      Source.canonicalRCEPPCitationBoundary
      true
      true
      true
      true)
  ≡ Governed.abstain
rceppCitationOnlyAuthorizationAbstains =
  ArtifactBridge.citationOnlyAuthorizationAbstains
    Source.canonicalRCEPPCitationHasNoArtifact
    true
    true
    true
    true

record RCEPPPromotionBoundary : Set where
  constructor rceppPromotionBoundary
  field
    citationIdentityAccepted : Bool
    artifactIdentityClosed : Bool
    legalOperationImported : Bool
    popularRecognitionImported : Bool
    canonicalPromotionAuthorized : Bool
    governedDecision : Governed.Decision
    governedDecisionIsAbstain : governedDecision ≡ Governed.abstain

canonicalRCEPPPromotionBoundary : RCEPPPromotionBoundary
canonicalRCEPPPromotionBoundary =
  rceppPromotionBoundary
    true
    false
    false
    false
    false
    Governed.abstain
    refl

canonicalRCEPPPromotionBoundaryReceipt :
  GenericReceipt.GenericReceipt
canonicalRCEPPPromotionBoundaryReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RCEPP promotion-spine boundary"
    "DASHI.Governance.Sudan.RCEPPPromotionBoundary"
    "rceppCitationOnlyAuthorizationAbstains"
    "threads the Charter citation boundary through the existing artifact-authority and governed-state promotion spine and proves quarantine/abstention even when all downstream closure bits are optimistic"
    "an authenticated artifact, operative constitutional authority and popular-recognition token remain absent"
    "agda -i . DASHI/Governance/Sudan/RCEPPPromotionBoundary.agda"
