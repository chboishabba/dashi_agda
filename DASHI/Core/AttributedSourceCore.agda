module DASHI.Core.AttributedSourceCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Reusable attributed-source surface.
--
-- This is the small common object for author/title/publication/DOI metadata.
-- A citation records provenance and a relationship to a formalisation.  It
-- does not import a theorem, prove agreement, or create domain authority.
------------------------------------------------------------------------

data DOIState : Set where
  doiRecorded : String → DOIState
  noDOIRecordedByAtlas : DOIState

data SourceKind : Set where
  academicArticleSource : SourceKind
  academicBookSource : SourceKind
  academicChapterSource : SourceKind
  practitionerSource : SourceKind
  communitySource : SourceKind
  institutionalSource : SourceKind
  governmentSource : SourceKind
  archivalSource : SourceKind
  technicalStandardSource : SourceKind
  newsSource : SourceKind
  namedSourceKind : String → SourceKind

data AttributionVisibility : Set where
  publicAttribution : AttributionVisibility
  controlledAttribution : AttributionVisibility
  existenceOnlyAttribution : AttributionVisibility

record AttributedSource : Set where
  constructor attributedSource
  field
    sourceAuthor : String
    sourceTitle : String
    publicationContext : String
    publicationYear : String
    doiState : DOIState
    canonicalURL : String
    sourceKind : SourceKind
    formalisationRelationship : String
    attributionVisibility : AttributionVisibility
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open AttributedSource public

mkDOISource :
  String → String → String → String → String → String →
  SourceKind → String → AttributionVisibility →
  AttributedSource
mkDOISource author title publication year doi url kind relationship visibility =
  attributedSource
    author
    title
    publication
    year
    (doiRecorded doi)
    url
    kind
    relationship
    visibility
    false
    refl
    false
    refl

mkNoDOISource :
  String → String → String → String → String →
  SourceKind → String → AttributionVisibility →
  AttributedSource
mkNoDOISource author title publication year url kind relationship visibility =
  attributedSource
    author
    title
    publication
    year
    noDOIRecordedByAtlas
    url
    kind
    relationship
    visibility
    false
    refl
    false
    refl

sourceCount : List AttributedSource → Nat
sourceCount [] = zero
sourceCount (_ ∷ sources) = suc (sourceCount sources)

record AttributedSourceAtlas : Set where
  constructor attributedSourceAtlas
  field
    atlasLabel : String
    atlasOwner : String
    sources : List AttributedSource
    atlasScope : String
    absentDOIClaimIsAtlasLocal : Bool
    absentDOIClaimIsAtlasLocalIsTrue : absentDOIClaimIsAtlasLocal ≡ true
    atlasCreatesAuthority : Bool
    atlasCreatesAuthorityIsFalse : atlasCreatesAuthority ≡ false

open AttributedSourceAtlas public

mkSourceAtlas :
  String → String → List AttributedSource → String →
  AttributedSourceAtlas
mkSourceAtlas label owner entries scope =
  attributedSourceAtlas
    label
    owner
    entries
    scope
    true
    refl
    false
    refl

record AttributionProjection
    (source : AttributedSource) : Set where
  constructor attributionProjection
  field
    publicLabel : String
    visibility : AttributionVisibility
    sourceStillIdentified : Bool
    sourceStillIdentifiedIsTrue : sourceStillIdentified ≡ true

open AttributionProjection public

mkPublicAttributionProjection :
  (source : AttributedSource) →
  String →
  AttributionProjection source
mkPublicAttributionProjection source label =
  attributionProjection label publicAttribution true refl

mkControlledAttributionProjection :
  (source : AttributedSource) →
  String →
  AttributionProjection source
mkControlledAttributionProjection source label =
  attributionProjection label controlledAttribution true refl

canonicalAttributedSourceCoreReceipt : GenericReceipt.GenericReceipt
canonicalAttributedSourceCoreReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "reusable attributed source core"
    "DASHI.Core.AttributedSourceCore"
    "AttributedSource / AttributedSourceAtlas / AttributionProjection"
    "centralises author, title, publication, DOI state, canonical URL, source kind, relationship, and attribution visibility"
    "a source citation does not import proof, agreement, endorsement, cultural authority, scientific authority, legal authority, or political authority"
    "agda -i . DASHI/Core/AttributedSourceCore.agda"

canonicalAttributedSourceCoreReceiptNonPromoting :
  GenericReceipt.promotesClaim canonicalAttributedSourceCoreReceipt ≡ false
canonicalAttributedSourceCoreReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse canonicalAttributedSourceCoreReceipt
