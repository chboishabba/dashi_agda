module DASHI.Reasoning.ReleasedArtifactProvenanceBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- RELEASED-ARTIFACT PROVENANCE BIDI
--
-- A document may be genuinely present in an official disclosure while the
-- text inside that document remains third-party material whose claims are not
-- thereby authored, endorsed, verified, or established by the disclosing
-- institution.
--
-- The motivating specimen is DOJ Epstein Library Data Set 9 document
-- EFTA01082667.  Its visible first page is titled "Illuminati Families and
-- Their Associates", attributes itself to "Matt of \"CC\"" and gives the date
-- 05 Sep 2008.  Later visible material identifies an extract from NEXUS
-- Magazine, Vol. 10 No. 3 (Apr-May 2003), copyright Will Banyan 2002/2003.
--
-- Source calibration:
--   https://www.justice.gov/epstein/files/DataSet%209/EFTA01082667.pdf
--
-- This module formalises provenance/inference boundaries only.  It does not
-- infer why the item entered a collection, who possessed/read/believed it,
-- or whether any substantive conspiracy claim in the embedded material is
-- true or false.
------------------------------------------------------------------------

data CarrierLayer : Set where
  embeddedMaterial : CarrierLayer
  collectedArtifact : CarrierLayer
  officialDisclosure : CarrierLayer

embeddedNotDisclosure : embeddedMaterial ≡ officialDisclosure → ⊥
embeddedNotDisclosure ()

collectionNotDisclosure : collectedArtifact ≡ officialDisclosure → ⊥
collectionNotDisclosure ()

------------------------------------------------------------------------
-- Distinct predicates that are often collapsed in social-media retellings.
------------------------------------------------------------------------

data ProvenancePredicate : Set where
  presentInOfficialRelease : ProvenancePredicate
  authoredByDisclosingInstitution : ProvenancePredicate
  endorsedByDisclosingInstitution : ProvenancePredicate
  verifiedByDisclosingInstitution : ProvenancePredicate
  independentlyEstablished : ProvenancePredicate

releaseNotAuthorship :
  presentInOfficialRelease ≡ authoredByDisclosingInstitution → ⊥
releaseNotAuthorship ()

releaseNotEndorsement :
  presentInOfficialRelease ≡ endorsedByDisclosingInstitution → ⊥
releaseNotEndorsement ()

releaseNotVerification :
  presentInOfficialRelease ≡ verifiedByDisclosingInstitution → ⊥
releaseNotVerification ()

releaseNotEstablished :
  presentInOfficialRelease ≡ independentlyEstablished → ⊥
releaseNotEstablished ()

------------------------------------------------------------------------
-- What can and cannot be read directly from an artifact.
------------------------------------------------------------------------

data AttributionStatus : Set where
  explicitThirdPartyAttribution : AttributionStatus
  institutionalAuthorship : AttributionStatus
  authorshipUnresolved : AttributionStatus

thirdPartyNotInstitutional :
  explicitThirdPartyAttribution ≡ institutionalAuthorship → ⊥
thirdPartyNotInstitutional ()

data VerificationStatus : Set where
  verificationUnresolved : VerificationStatus
  independentlyVerified : VerificationStatus
  independentlyRefuted : VerificationStatus

unresolvedNotVerified : verificationUnresolved ≡ independentlyVerified → ⊥
unresolvedNotVerified ()

unresolvedNotRefuted : verificationUnresolved ≡ independentlyRefuted → ⊥
unresolvedNotRefuted ()

data CustodyInterpretation : Set where
  custodyRouteUnresolved : CustodyInterpretation
  directReceiptEstablished : CustodyInterpretation
  downloadEstablished : CustodyInterpretation
  forwardingEstablished : CustodyInterpretation
  seizureContextEstablished : CustodyInterpretation

custodyUnknownNotDirectReceipt :
  custodyRouteUnresolved ≡ directReceiptEstablished → ⊥
custodyUnknownNotDirectReceipt ()

------------------------------------------------------------------------
-- The release surface and the source surface are deliberately separate.
------------------------------------------------------------------------

record ReleaseSurface : Set where
  constructor releaseSurface
  field
    releaseIdentifier : String
    releaseDataset : String
    releasedByOfficialLibrary : Bool

open ReleaseSurface public

record EmbeddedSourceSurface : Set where
  constructor embeddedSourceSurface
  field
    visibleTitle : String
    visibleFrom : String
    visibleDate : String
    nestedPublication : String
    attribution : AttributionStatus

open EmbeddedSourceSurface public

record ReleasedArtifact : Set where
  constructor releasedArtifact
  field
    release : ReleaseSurface
    embedded : EmbeddedSourceSurface
    custodyInterpretation : CustodyInterpretation
    claimVerification : VerificationStatus

open ReleasedArtifact public

------------------------------------------------------------------------
-- Concrete bounded specimen from the released file.
------------------------------------------------------------------------

efta01082667Release : ReleaseSurface
efta01082667Release =
  releaseSurface
    "EFTA01082667"
    "Data Set 9"
    true

efta01082667Embedded : EmbeddedSourceSurface
efta01082667Embedded =
  embeddedSourceSurface
    "Illuminati Families and Their Associates"
    "Matt of \"CC\""
    "05 Sep 2008, 15:00"
    "NEXUS Magazine, Volume 10, Number 3 (April-May 2003); Will Banyan, 2002/2003"
    explicitThirdPartyAttribution

efta01082667 : ReleasedArtifact
efta01082667 =
  releasedArtifact
    efta01082667Release
    efta01082667Embedded
    custodyRouteUnresolved
    verificationUnresolved

releasePresenceIsTrue :
  releasedByOfficialLibrary (release efta01082667) ≡ true
releasePresenceIsTrue = refl

embeddedAttributionIsThirdParty :
  attribution (embedded efta01082667) ≡ explicitThirdPartyAttribution
embeddedAttributionIsThirdParty = refl

custodyRouteRemainsUnresolved :
  custodyInterpretation efta01082667 ≡ custodyRouteUnresolved
custodyRouteRemainsUnresolved = refl

substantiveVerificationRemainsUnresolved :
  claimVerification efta01082667 ≡ verificationUnresolved
substantiveVerificationRemainsUnresolved = refl

------------------------------------------------------------------------
-- Forward direction:
--
--   source material -> collected artifact -> official disclosure
--
-- preserves inclusion/provenance, but does not strengthen the embedded claim.
------------------------------------------------------------------------

record ForwardReleaseTrace : Set where
  constructor forwardReleaseTrace
  field
    sourceLayer : CarrierLayer
    collectionLayer : CarrierLayer
    disclosureLayer : CarrierLayer
    sourceLayerIsEmbedded : sourceLayer ≡ embeddedMaterial
    collectionLayerIsCollected : collectionLayer ≡ collectedArtifact
    disclosureLayerIsOfficial : disclosureLayer ≡ officialDisclosure
    disclosurePresence : ProvenancePredicate
    disclosurePresenceIsRelease :
      disclosurePresence ≡ presentInOfficialRelease

open ForwardReleaseTrace public

canonicalForwardTrace : ForwardReleaseTrace
canonicalForwardTrace =
  forwardReleaseTrace
    embeddedMaterial
    collectedArtifact
    officialDisclosure
    refl refl refl
    presentInOfficialRelease
    refl

------------------------------------------------------------------------
-- Backward direction:
--
--   official disclosure -> ? source/meaning/verification
--
-- is partial.  The outer release carrier does not recover authorship,
-- endorsement, verification, custody route, or truth of embedded assertions.
------------------------------------------------------------------------

data BackwardInferenceStatus : Set where
  provenanceRecovered : BackwardInferenceStatus
  provenancePartiallyRecovered : BackwardInferenceStatus
  inferenceBlocked : BackwardInferenceStatus

blockedNotRecovered : inferenceBlocked ≡ provenanceRecovered → ⊥
blockedNotRecovered ()

record BackwardReleaseAudit : Set where
  constructor backwardReleaseAudit
  field
    releasePresenceRecovered : Bool
    embeddedAttributionRecovered : AttributionStatus
    custodyRecovered : CustodyInterpretation
    verificationRecovered : VerificationStatus
    authorshipPromotionBlocked : Bool
    endorsementPromotionBlocked : Bool
    verificationPromotionBlocked : Bool
    truthPromotionBlocked : Bool
    status : BackwardInferenceStatus

open BackwardReleaseAudit public

canonicalBackwardAudit : BackwardReleaseAudit
canonicalBackwardAudit =
  backwardReleaseAudit
    true
    explicitThirdPartyAttribution
    custodyRouteUnresolved
    verificationUnresolved
    true true true true
    provenancePartiallyRecovered

------------------------------------------------------------------------
-- Non-factorability witnesses.
--
-- Two artifacts can have the exact same official-release surface while their
-- verification state differs.  Therefore no decoder from release-surface alone
-- can generically recover verification.
------------------------------------------------------------------------

verifiedCounterfactual : ReleasedArtifact
verifiedCounterfactual =
  releasedArtifact
    efta01082667Release
    efta01082667Embedded
    custodyRouteUnresolved
    independentlyVerified

sameReleaseSurfaceDifferentVerification :
  (decode : ReleaseSurface → VerificationStatus) →
  decode efta01082667Release ≡ verificationUnresolved →
  decode efta01082667Release ≡ independentlyVerified →
  ⊥
sameReleaseSurfaceDifferentVerification decode first second =
  unresolvedNotVerified (trans (sym first) second)

receivedCounterfactual : ReleasedArtifact
receivedCounterfactual =
  releasedArtifact
    efta01082667Release
    efta01082667Embedded
    directReceiptEstablished
    verificationUnresolved

sameReleaseSurfaceDifferentCustody :
  (decode : ReleaseSurface → CustodyInterpretation) →
  decode efta01082667Release ≡ custodyRouteUnresolved →
  decode efta01082667Release ≡ directReceiptEstablished →
  ⊥
sameReleaseSurfaceDifferentCustody decode first second =
  custodyUnknownNotDirectReceipt (trans (sym first) second)

------------------------------------------------------------------------
-- BIDI weld: the forward and backward views must refer to the exact same
-- release surface.  This permits provenance recovery without semantic
-- promotion.
------------------------------------------------------------------------

record ReleasedArtifactBidi : Set where
  constructor releasedArtifactBidi
  field
    artifact : ReleasedArtifact
    forward : ForwardReleaseTrace
    backward : BackwardReleaseAudit
    forwardReleaseSurface : ReleaseSurface
    backwardReleaseSurface : ReleaseSurface
    forwardIsArtifactRelease : forwardReleaseSurface ≡ release artifact
    backwardIsArtifactRelease : backwardReleaseSurface ≡ release artifact
    sameReleaseSurface : forwardReleaseSurface ≡ backwardReleaseSurface

open ReleasedArtifactBidi public

canonicalEftaBidi : ReleasedArtifactBidi
canonicalEftaBidi =
  releasedArtifactBidi
    efta01082667
    canonicalForwardTrace
    canonicalBackwardAudit
    efta01082667Release
    efta01082667Release
    refl refl refl

------------------------------------------------------------------------
-- Promotion boundary summary.
------------------------------------------------------------------------

record ReleasedArtifactPromotionBoundary : Set where
  constructor releasedArtifactPromotionBoundary
  field
    officialReleaseImpliesInstitutionalAuthorship : Bool
    officialReleaseImpliesInstitutionalEndorsement : Bool
    officialReleaseImpliesInstitutionalVerification : Bool
    officialReleaseImpliesEmbeddedClaimTrue : Bool
    titleRecoversCustodyRoute : Bool
    titleRecoversBeliefOrEndorsement : Bool
    oldEmbeddedPublicationBecomesNewOfficialAuthorship : Bool

canonicalReleasedArtifactPromotionBoundary : ReleasedArtifactPromotionBoundary
canonicalReleasedArtifactPromotionBoundary =
  releasedArtifactPromotionBoundary
    false false false false false false false
