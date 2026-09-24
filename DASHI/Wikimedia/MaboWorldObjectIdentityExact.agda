module DASHI.Wikimedia.MaboWorldObjectIdentityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- WORLD IDENTITY IS NOT REPRESENTATION IDENTITY
--
-- P7d counts reviewed world-object identity classes.  QIDs, Wikipedia URLs,
-- provider IDs and legal-source IDs remain representations/manifestations and
-- may be reviewed as aliases without incrementing novelty twice.
------------------------------------------------------------------------

record WorldObjectIdentity : Set where
  constructor world-object-identity
  field
    identityClassReference : String
    primaryRepresentation : String
    qidRepresentation : String
    articleRepresentation : String
    providerRepresentation : String

open WorldObjectIdentity public

data IdentityResolutionKind : Set where
  exactSameRepresentation : IdentityResolutionKind
  sameObjectDifferentRepresentation : IdentityResolutionKind
  relatedObject : IdentityResolutionKind
  ambiguousIdentity : IdentityResolutionKind
  wrongIdentityType : IdentityResolutionKind
  unresolvedIdentity : IdentityResolutionKind

record WorldIdentityResolutionReceipt : Set where
  constructor world-identity-resolution-receipt
  field
    resolutionReference : String
    resolvedIdentity : WorldObjectIdentity
    resolutionKind : IdentityResolutionKind
    evidenceReference : String
    countingIdentityClass : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open WorldIdentityResolutionReceipt public

mkSameObjectResolution :
  String → WorldObjectIdentity → String → WorldIdentityResolutionReceipt
mkSameObjectResolution receipt identity evidence =
  world-identity-resolution-receipt
    receipt
    identity
    sameObjectDifferentRepresentation
    evidence
    (identityClassReference identity)
    true refl false refl false refl false refl

------------------------------------------------------------------------
-- Concrete Mabo participant identity-class fixture.
--
-- The QID/article alignment is a reviewed same-object coordinate for novelty
-- accounting.  It does not turn Wikidata/Wikipedia into legal authority.
------------------------------------------------------------------------

eddieMaboIdentity : WorldObjectIdentity
eddieMaboIdentity =
  world-object-identity
    "world-object:eddie-mabo"
    "Q975866"
    "Q975866"
    "https://en.wikipedia.org/wiki/Eddie_Mabo"
    "mabo:participant:eddie-mabo"

maboEddieParticipantResolution : WorldIdentityResolutionReceipt
maboEddieParticipantResolution =
  mkSameObjectResolution
    "identity-resolution:mabo:eddie"
    eddieMaboIdentity
    "reviewed QID/article same-object evidence; representation alias only"

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data RepresentationIdentityEqualsWorldIdentity : Set where
data QidAloneDeterminesWorldIdentity : Set where
data ArticleUrlAloneDeterminesWorldIdentity : Set where
data SameObjectResolutionCreatesLegalAuthority : Set where
data SameObjectResolutionCreatesClaimTruth : Set where

data HundredRepresentationStringsEqualsHundredWorldObjects : Set where

representationIdentityDoesNotEqualWorldIdentity :
  RepresentationIdentityEqualsWorldIdentity → ⊥
representationIdentityDoesNotEqualWorldIdentity ()

qidAloneDoesNotDetermineWorldIdentity :
  QidAloneDeterminesWorldIdentity → ⊥
qidAloneDoesNotDetermineWorldIdentity ()

articleUrlAloneDoesNotDetermineWorldIdentity :
  ArticleUrlAloneDeterminesWorldIdentity → ⊥
articleUrlAloneDoesNotDetermineWorldIdentity ()

sameObjectResolutionDoesNotCreateLegalAuthority :
  SameObjectResolutionCreatesLegalAuthority → ⊥
sameObjectResolutionDoesNotCreateLegalAuthority ()

sameObjectResolutionDoesNotCreateClaimTruth :
  SameObjectResolutionCreatesClaimTruth → ⊥
sameObjectResolutionDoesNotCreateClaimTruth ()

hundredRepresentationStringsDoNotEqualHundredWorldObjects :
  HundredRepresentationStringsEqualsHundredWorldObjects → ⊥
hundredRepresentationStringsDoNotEqualHundredWorldObjects ()
