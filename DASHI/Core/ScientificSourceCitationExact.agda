module DASHI.Core.ScientificSourceCitationExact where

------------------------------------------------------------------------
-- SCIENTIFIC SOURCE CITATION / IDENTIFIER HIERARCHY
--
-- Implements Docs/SourceAttributionPolicy.md for person/work attribution.
-- Preferred recovery order:
--   DOI -> stable scholarly/standards identifier -> canonical institutional or
--   repository identifier/URL -> author + title + venue/year -> best remaining
--   recoverable provenance.
--
-- No DOI is fabricated merely to make a registry uniform.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- Identifier carrier.
------------------------------------------------------------------------

data StableIdentifier : Set where
  doi : String → StableIdentifier
  pmid : String → StableIdentifier
  pmcid : String → StableIdentifier
  arxiv : String → StableIdentifier
  patentPublication : String → StableIdentifier
  nasaNTRS : String → StableIdentifier
  institutionalDocumentId : String → StableIdentifier
  canonicalURL : String → StableIdentifier
  bibliographicFallback : String → StableIdentifier
  : StableIdentifier

data CitationRole : Set where
  authorshipSource
  inventorshipSource
  projectRoleSource
  institutionalRoleSource
  researchAreaSource
  relationshipClaimSource
  rosterScopeSource
  identityCandidateSource
  : CitationRole

record ScientificCitation : Set where
  constructor scientific-citation
  field
    authorsOrInstitution : String
    title : String
    venueOrPublisher : String
    year : Nat
    identifier : StableIdentifier
    exactLocator : String
    citationRole : CitationRole
    boundedClaim : String

open ScientificCitation public

record AttributionWithCitation : Set where
  constructor attribution-with-citation
  field
    attribution : Attribution.ScientificWorkAttribution
    citation : ScientificCitation

open AttributionWithCitation public

------------------------------------------------------------------------
-- Policy boundary.
------------------------------------------------------------------------

record ScientificCitationBoundary : Set where
  constructor scientific-citation-boundary
  field
    doiPreferredWhenVerified : Bool
    doiPreferredWhenVerifiedIsTrue : doiPreferredWhenVerified ≡ true
    noDOIMeansSourceMustBeDropped : Bool
    noDOIMeansSourceMustBeDroppedIsFalse : noDOIMeansSourceMustBeDropped ≡ false
    canonicalInstitutionalIdentifierIsValidFallback : Bool
    canonicalInstitutionalIdentifierIsValidFallbackIsTrue :
      canonicalInstitutionalIdentifierIsValidFallback ≡ true
    authorTitleVenueYearIsValidFallback : Bool
    authorTitleVenueYearIsValidFallbackIsTrue :
      authorTitleVenueYearIsValidFallback ≡ true
    citationTransfersProofAuthority : Bool
    citationTransfersProofAuthorityIsFalse : citationTransfersProofAuthority ≡ false
    citationTransfersDASHITheoremAuthorship : Bool
    citationTransfersDASHITheoremAuthorshipIsFalse :
      citationTransfersDASHITheoremAuthorship ≡ false

canonicalScientificCitationBoundary : ScientificCitationBoundary
canonicalScientificCitationBoundary =
  scientific-citation-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
