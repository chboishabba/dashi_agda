module DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityAdmissibilityV02Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairProofSearchBridgeV02Exact as Bridge
import DASHI.Governance.NativeTitleAuthorityLayerExact as NativeTitle
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Envelope

------------------------------------------------------------------------
-- COMMUNITY AUTHORITY ADMISSIBILITY V02
--
-- An authority receipt is consumer- and outcome-relative.  Statutory legal
-- carriers are useful authority coordinates but cannot impersonate the whole
-- Traditional Owner community or exhaust sovereign/cultural authority.
------------------------------------------------------------------------

data AuthorityAdmissibility : Set where
  authorityCandidate
  authorityAdmittedForConsumer
  authorityRejectedForConsumer
  : AuthorityAdmissibility

record CommunityAuthorityReceiptV02 : Set where
  constructor community-authority-receipt-v02
  field
    consumerReference : String
    outcomeReference : String
    authorityRole : NativeTitle.AuthorityRole
    authorityEnvelope : Envelope.AuthorityEnvelope
    admissibility : AuthorityAdmissibility
    roleScopeReference : String
    mandateReference : String
    temporalScopeReference : String
    provenanceReference : String
    roleEqualsWholeCommunityByDefault : Bool
    roleEqualsWholeCommunityByDefaultIsFalse : roleEqualsWholeCommunityByDefault ≡ false
    statutoryRepresentationEqualsSovereignty : Bool
    statutoryRepresentationEqualsSovereigntyIsFalse : statutoryRepresentationEqualsSovereignty ≡ false
    sourceExistenceAloneAdmitsAuthority : Bool
    sourceExistenceAloneAdmitsAuthorityIsFalse : sourceExistenceAloneAdmitsAuthority ≡ false

open CommunityAuthorityReceiptV02 public

rntbcAuthorityCandidate : CommunityAuthorityReceiptV02
rntbcAuthorityCandidate = community-authority-receipt-v02
  "native-title rights-management consumer"
  "manage recognised native-title rights and interests for the selected determination"
  NativeTitle.registeredNativeTitleBodyCorporate
  Envelope.externalPublishedDescription
  authorityCandidate
  "RNTBC statutory representation/management role only"
  "specific current mandate must be established from the relevant corporation/community material"
  "current mandate interval unresolved in this generic fixture"
  "Native Title Act/ORIC role provenance retained"
  false refl
  false refl
  false refl

traditionalOwnerAuthorityCandidate : CommunityAuthorityReceiptV02
traditionalOwnerAuthorityCandidate = community-authority-receipt-v02
  "Country/community governance consumer"
  "community-defined Country outcome; exact outcome and mandate correspondence required"
  NativeTitle.traditionalOwnerCommunity
  Envelope.communityResearchEnvelope
  authorityCandidate
  "Traditional Owner community role; not equated with statutory corporate personality"
  "consumer-specific authorised decision/outcome still required"
  "present authority scope must be source-established"
  "community-origin/protocol/governance coordinates retained"
  false refl
  false refl
  false refl

traditionalOwnerRoleIsNotRntbc :
  NativeTitle.traditionalOwnerCommunity ≡ NativeTitle.registeredNativeTitleBodyCorporate → ⊥
traditionalOwnerRoleIsNotRntbc = NativeTitle.communityIsNotRntbc

legalRecognitionDoesNotExhaustCommunityAuthority :
  NativeTitle.legalRecognitionExhaustsCommunityAuthority
    NativeTitle.canonicalNativeTitleAuthorityBoundary ≡ false
legalRecognitionDoesNotExhaustCommunityAuthority = refl

statutoryRepresentationDoesNotEqualSovereignty :
  NativeTitle.statutoryRepresentationEqualsSovereignty
    NativeTitle.canonicalNativeTitleAuthorityBoundary ≡ false
statutoryRepresentationDoesNotEqualSovereignty = refl

------------------------------------------------------------------------
-- Admission compiler.  The caller must supply the same-consumer/outcome,
-- mandate, temporal and provenance receipts; this module does not manufacture
-- them from the role label.
------------------------------------------------------------------------

record AuthorityAdmissionEvidence (candidate : CommunityAuthorityReceiptV02) : Set₁ where
  constructor authority-admission-evidence
  field
    sameConsumerAndOutcome : Set
    mandateWithinRoleScope : Set
    mandateCurrentlyValid : Set
    provenancePreserved : Set
    admissionReference : String

record AdmittedCommunityAuthorityV02 (candidate : CommunityAuthorityReceiptV02) : Set₁ where
  constructor admitted-community-authority-v02
  field
    evidence : AuthorityAdmissionEvidence candidate
    authorityResidualAfterReference : String
    authorityPaymentReference : String

admitAuthority :
  (candidate : CommunityAuthorityReceiptV02) →
  AuthorityAdmissionEvidence candidate →
  AdmittedCommunityAuthorityV02 candidate
admitAuthority candidate evidence = admitted-community-authority-v02
  evidence
  "next residual determined by consumer-specific operational recomputation"
  "authority admitted only for the receipt's declared consumer/outcome"

------------------------------------------------------------------------
-- Proof-search compatibility.
------------------------------------------------------------------------

communityAuthorityProducerIsAttributionNotLegalAuthorityDiscovery :
  Bridge.producerFor Bridge.communityAuthorityCapacityResidualV02
  ≡ DASHI.Law.SensibLawProofDirectedSearchIntentExact.attributionProducer
communityAuthorityProducerIsAttributionNotLegalAuthorityDiscovery = refl

data RNTBCRolePaysWholeCommunityAuthority : Set where
data PBCResourceEvidencePaysOutcomeAuthority : Set where
data AuthorityEnvelopeAutomaticallyAdmitsMandate : Set where

rntbcDoesNotPayWholeCommunityAuthority : RNTBCRolePaysWholeCommunityAuthority → ⊥
rntbcDoesNotPayWholeCommunityAuthority ()

pbcResourceEvidenceDoesNotPayOutcomeAuthority : PBCResourceEvidencePaysOutcomeAuthority → ⊥
pbcResourceEvidenceDoesNotPayOutcomeAuthority ()

authorityEnvelopeDoesNotAutomaticallyAdmitMandate :
  AuthorityEnvelopeAutomaticallyAdmitsMandate → ⊥
authorityEnvelopeDoesNotAutomaticallyAdmitMandate ()
