module DASHI.Interop.SourceAttributionShapePolicyExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION SHAPE POLICY
--
-- "Attach a source" is not one universal storage operation. Different source
-- carriers require different provenance shapes. This prevents both under-
-- attribution and cargo-cult bibliographic metadata on internal/code/archive
-- objects that are better identified by hash/path/revision.
------------------------------------------------------------------------

data SourceBearingObjectKind : Set where
  publishedEmpiricalClaim : SourceBearingObjectKind
  publishedScientificTheorem : SourceBearingObjectKind
  judicialOrLegislativeAuthority : SourceBearingObjectKind
  interpretiveOrCulturalSource : SourceBearingObjectKind
  communityKnowledgeOrAuthority : SourceBearingObjectKind
  localArchiveOrCodeContract : SourceBearingObjectKind
  wikidataReferenceCandidate : SourceBearingObjectKind
  providerOrRuntimeSurface : SourceBearingObjectKind
  internalDerivedTheorem : SourceBearingObjectKind

data RequiredAttributionShape : Set where
  attributedSourcePlusDiligence : RequiredAttributionShape
  attributedSourcePlusTheoremMatch : RequiredAttributionShape
  attributedSourcePlusExactLegalSpan : RequiredAttributionShape
  attributedSourcePlusInterpretationBoundary : RequiredAttributionShape
  communityProvenancePlusAuthorityMandate : RequiredAttributionShape
  contentHashPathRevisionProvenance : RequiredAttributionShape
  candidateThenInspectedAttributedSource : RequiredAttributionShape
  implementationReceiptPlusAuthorityBoundary : RequiredAttributionShape
  proofLineageNoNewExternalCitation : RequiredAttributionShape

requiredAttributionShape : SourceBearingObjectKind → RequiredAttributionShape
requiredAttributionShape publishedEmpiricalClaim = attributedSourcePlusDiligence
requiredAttributionShape publishedScientificTheorem = attributedSourcePlusTheoremMatch
requiredAttributionShape judicialOrLegislativeAuthority = attributedSourcePlusExactLegalSpan
requiredAttributionShape interpretiveOrCulturalSource = attributedSourcePlusInterpretationBoundary
requiredAttributionShape communityKnowledgeOrAuthority = communityProvenancePlusAuthorityMandate
requiredAttributionShape localArchiveOrCodeContract = contentHashPathRevisionProvenance
requiredAttributionShape wikidataReferenceCandidate = candidateThenInspectedAttributedSource
requiredAttributionShape providerOrRuntimeSurface = implementationReceiptPlusAuthorityBoundary
requiredAttributionShape internalDerivedTheorem = proofLineageNoNewExternalCitation

------------------------------------------------------------------------
-- Firewalls against the two symmetric attribution errors.
------------------------------------------------------------------------

data EverySourceNeedsDOI : Set where
data InternalTheoremNeedsFreshBibliography : Set where
data HashedArchiveShouldPretendToBePublishedArticle : Set where
data BibliographicCitationReplacesCommunityAuthority : Set where
data RuntimeReceiptCreatesSourceAuthority : Set where

notEverySourceHasOrNeedsDOI : EverySourceNeedsDOI → ⊥
notEverySourceHasOrNeedsDOI ()

internalProofUsesLineageNotCitationCargoCult : InternalTheoremNeedsFreshBibliography → ⊥
internalProofUsesLineageNotCitationCargoCult ()

archiveIdentityRemainsArchiveIdentity : HashedArchiveShouldPretendToBePublishedArticle → ⊥
archiveIdentityRemainsArchiveIdentity ()

communityAuthorityRequiresMoreThanCitation :
  BibliographicCitationReplacesCommunityAuthority → ⊥
communityAuthorityRequiresMoreThanCitation ()

runtimeReceiptDoesNotCreateExternalAuthority : RuntimeReceiptCreatesSourceAuthority → ⊥
runtimeReceiptDoesNotCreateExternalAuthority ()

record SourceAttributionShapeBoundary : Set where
  constructor source-attribution-shape-boundary
  field
    attributionShapeIsCarrierSensitive : Bool
    attributionShapeIsCarrierSensitiveIsTrue : attributionShapeIsCarrierSensitive ≡ true
    primaryPublishedClaimsUseCanonicalAttributedSource : Bool
    primaryPublishedClaimsUseCanonicalAttributedSourceIsTrue :
      primaryPublishedClaimsUseCanonicalAttributedSource ≡ true
    localArchivesMayUseHashPathRevisionInstead : Bool
    localArchivesMayUseHashPathRevisionInsteadIsTrue :
      localArchivesMayUseHashPathRevisionInstead ≡ true
    internalDerivationsNeedFreshExternalCitation : Bool
    internalDerivationsNeedFreshExternalCitationIsFalse :
      internalDerivationsNeedFreshExternalCitation ≡ false

canonicalSourceAttributionShapeBoundary : SourceAttributionShapeBoundary
canonicalSourceAttributionShapeBoundary =
  source-attribution-shape-boundary true refl true refl true refl false refl
