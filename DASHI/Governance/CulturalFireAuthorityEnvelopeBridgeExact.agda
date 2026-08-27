module DASHI.Governance.CulturalFireAuthorityEnvelopeBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Envelope
import DASHI.Governance.SteffensenCulturalFireAuthorityExact as Fire

------------------------------------------------------------------------
-- CULTURAL FIRE -> EXISTING INDIGENOUS AUTHORITY ENVELOPE
--
-- The source-specific Firesticks/Steffensen witness now consumes the existing
-- provenance/governance/protocol/permission/sovereign-standing architecture.
------------------------------------------------------------------------

custodianEnvelope : Envelope.AuthorityEnvelope
custodianEnvelope = Envelope.authorityEnvelope
  Envelope.communityOrigin
  Envelope.communityControlled
  Envelope.protocolSpecified
  Envelope.interventionPermitted
  Envelope.originatingAuthority

externalTechniqueEnvelope : Envelope.AuthorityEnvelope
externalTechniqueEnvelope = Envelope.authorityEnvelope
  Envelope.externalDescription
  Envelope.externalGovernance
  Envelope.protocolUnspecified
  Envelope.permissionUnspecified
  Envelope.externalObserverStanding

externalTechniqueIsNotOriginatingAuthority :
  Envelope.AuthorityEnvelope.sovereignStanding externalTechniqueEnvelope ≡
  Envelope.originatingAuthority → ⊥
externalTechniqueIsNotOriginatingAuthority ()

externalTechniqueHasNoInterventionPermission :
  Envelope.AuthorityEnvelope.permission externalTechniqueEnvelope ≡
  Envelope.interventionPermitted → ⊥
externalTechniqueHasNoInterventionPermission ()

sourceLevelPracticeWithoutAuthority :
  DASHI.Core.KnowledgeContentAuthoritySeparationExact.PracticeWithoutAuthority Fire.system
sourceLevelPracticeWithoutAuthority = Fire.trainedTechniqueWithoutAuthority

record CulturalFireEnvelopeBoundary : Set where
  constructor culturalFireEnvelopeBoundary
  field
    techniqueReceiptEqualsAuthorityEnvelope : Bool
    techniqueReceiptEqualsAuthorityEnvelopeIsFalse : techniqueReceiptEqualsAuthorityEnvelope ≡ false
    institutionalTrainingTransfersSovereignty : Bool
    institutionalTrainingTransfersSovereigntyIsFalse : institutionalTrainingTransfersSovereignty ≡ false
    protocolCanBeDroppedAfterKnowledgeTransfer : Bool
    protocolCanBeDroppedAfterKnowledgeTransferIsFalse : protocolCanBeDroppedAfterKnowledgeTransfer ≡ false

canonicalCulturalFireEnvelopeBoundary : CulturalFireEnvelopeBoundary
canonicalCulturalFireEnvelopeBoundary = culturalFireEnvelopeBoundary false refl false refl false refl
