module DASHI.Wikimedia.NativeReferenceSemanticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Wikimedia.AristotleNativeModelSourceExact as Aristotle

------------------------------------------------------------------------
-- NATIVE WIKIDATA REFERENCE-SNAK SEMANTICS
--
-- P248 / stated in and P854 / reference URL can identify source candidates.
-- P143 / imported from Wikimedia project is provenance-only.  None creates
-- source authority, admissibility or truth by itself.
------------------------------------------------------------------------

p248 : Id.PropertyId
p248 = Id.propertyId "P248"
p854 : Id.PropertyId
p854 = Id.propertyId "P854"
p143 : Id.PropertyId
p143 = Id.propertyId "P143"

data NativeReferenceKind : Set where
  statedInReference referenceUrlReference importedFromReference otherReference
  : NativeReferenceKind

propertyForReferenceKind : NativeReferenceKind → Id.PropertyId
propertyForReferenceKind statedInReference = p248
propertyForReferenceKind referenceUrlReference = p854
propertyForReferenceKind importedFromReference = p143
propertyForReferenceKind otherReference = Id.propertyId "OTHER"

data ReferenceSourceRole : Set where
  sourceCandidate provenanceOnly unresolvedReferenceRole : ReferenceSourceRole

sourceRole : NativeReferenceKind → ReferenceSourceRole
sourceRole statedInReference = sourceCandidate
sourceRole referenceUrlReference = sourceCandidate
sourceRole importedFromReference = provenanceOnly
sourceRole otherReference = unresolvedReferenceRole

record ClassifiedReferenceSnak : Set where
  constructor classified-reference-snak
  field
    nativeSnak : WD.ReferenceSnak
    referenceKind : NativeReferenceKind
    propertyMatches : WD.referenceProperty nativeSnak ≡ propertyForReferenceKind referenceKind
    role : ReferenceSourceRole
    roleMatches : role ≡ sourceRole referenceKind
    classificationReference : String
open ClassifiedReferenceSnak public

p248SourceCandidate :
  (snak : WD.ReferenceSnak) →
  WD.referenceProperty snak ≡ p248 →
  ClassifiedReferenceSnak
p248SourceCandidate snak refl =
  classified-reference-snak snak statedInReference refl sourceCandidate refl
    "P248/stated-in classified as external referenced-source candidate; authority remains downstream"

p854SourceCandidate :
  (snak : WD.ReferenceSnak) →
  WD.referenceProperty snak ≡ p854 →
  ClassifiedReferenceSnak
p854SourceCandidate snak refl =
  classified-reference-snak snak referenceUrlReference refl sourceCandidate refl
    "P854/reference-URL classified as external referenced-source candidate; content still requires inspection"

p143ProvenanceOnly :
  (snak : WD.ReferenceSnak) →
  WD.referenceProperty snak ≡ p143 →
  ClassifiedReferenceSnak
p143ProvenanceOnly snak refl =
  classified-reference-snak snak importedFromReference refl provenanceOnly refl
    "P143/imported-from is provenance-only, matching Aristotle RefKind.reliable"

importedFromSourceContract : Aristotle.AristotleDeclarationContract
importedFromSourceContract = Aristotle.importedFromReliabilityContract

record ReferenceSourceCandidate : Set where
  constructor reference-source-candidate
  field
    classified : ClassifiedReferenceSnak
    candidateReceipt : Source.SourceReceipt
    roleIsSourceCandidate : role classified ≡ sourceCandidate
    candidateReceiptIsExternalReferencedSource :
      Source.layer candidateReceipt ≡ Source.externalReferencedSourceLayer
    candidateReference : String
open ReferenceSourceCandidate public

externalSourceCandidate :
  (classified : ClassifiedReferenceSnak) →
  role classified ≡ sourceCandidate →
  (receipt : Source.SourceReceipt) →
  Source.layer receipt ≡ Source.externalReferencedSourceLayer →
  String →
  ReferenceSourceCandidate
externalSourceCandidate classified roleProof receipt layerProof ref =
  reference-source-candidate classified receipt roleProof layerProof ref

data ReferenceCandidateCreatesAuthority : Set where
data ImportedFromCreatesAuthority : Set where
data ReferenceUrlVerifiesItsContent : Set where
data StatedInMakesContainingStatementTrue : Set where

aReferenceCandidateDoesNotCreateAuthority : ReferenceCandidateCreatesAuthority → ⊥
aReferenceCandidateDoesNotCreateAuthority ()
importedFromDoesNotCreateAuthority : ImportedFromCreatesAuthority → ⊥
importedFromDoesNotCreateAuthority ()
referenceUrlDoesNotVerifyContent : ReferenceUrlVerifiesItsContent → ⊥
referenceUrlDoesNotVerifyContent ()
statedInDoesNotMakeStatementTrue : StatedInMakesContainingStatementTrue → ⊥
statedInDoesNotMakeStatementTrue ()

record NativeReferenceBoundary : Set where
  constructor native-reference-boundary
  field
    p248CanIdentifySourceCandidate : Bool
    p854CanIdentifySourceCandidate : Bool
    p143IsProvenanceOnly : Bool
    sourceCandidateRequiresExternalSourceReceipt : Bool
    sourceCandidateCreatesAuthority : Bool
    importedFromCreatesAuthority : Bool

canonicalNativeReferenceBoundary : NativeReferenceBoundary
canonicalNativeReferenceBoundary =
  native-reference-boundary true true true true false false
