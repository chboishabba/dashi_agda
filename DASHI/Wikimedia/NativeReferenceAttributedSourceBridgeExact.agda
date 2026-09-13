module DASHI.Wikimedia.NativeReferenceAttributedSourceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attributed
import DASHI.Wikimedia.NativeReferenceSemanticsExact as Native

------------------------------------------------------------------------
-- NATIVE REFERENCE CANDIDATE -> ATTRIBUTED SOURCE BRIDGE
--
-- P248/P854 classification only establishes a source candidate.  Promotion to
-- the repository's canonical bibliographic carrier requires separate author /
-- title / publication metadata plus an exact same-source and inspection weld.
------------------------------------------------------------------------

record AttributedReferenceSource
    (candidate : Native.ReferenceSourceCandidate) : Set where
  constructor attributed-reference-source
  field
    source : Attributed.AttributedSource
    nativeReferenceMatchesAttributedSourceReceipt : Set
    referencedContentInspectedReceipt : Set
    propositionLocatorReference : String
    sourceRevisionReference : String
    attributionReference : String

open AttributedReferenceSource public

data ReferenceCandidateAutomaticallyAttributed : Set where
data P854AutomaticallyVerifiesCanonicalURL : Set where
data P248AutomaticallySuppliesAuthorTitle : Set where
data AttributedReferenceAutomaticallyPaysProposition : Set where

candidateDoesNotCreateAttributedSource :
  ReferenceCandidateAutomaticallyAttributed → ⊥
candidateDoesNotCreateAttributedSource ()

p854DoesNotVerifyCanonicalURL : P854AutomaticallyVerifiesCanonicalURL → ⊥
p854DoesNotVerifyCanonicalURL ()

p248DoesNotManufactureBibliography : P248AutomaticallySuppliesAuthorTitle → ⊥
p248DoesNotManufactureBibliography ()

attributionStillDoesNotPayProposition :
  AttributedReferenceAutomaticallyPaysProposition → ⊥
attributionStillDoesNotPayProposition ()

record NativeReferenceAttributedSourceBoundary : Set where
  constructor native-reference-attributed-source-boundary
  field
    nativeSourceCandidateAndAttributedSourceAreDistinct : Bool
    nativeSourceCandidateAndAttributedSourceAreDistinctIsTrue :
      nativeSourceCandidateAndAttributedSourceAreDistinct ≡ true
    exactSameSourceWeldRequired : Bool
    exactSameSourceWeldRequiredIsTrue : exactSameSourceWeldRequired ≡ true
    referencedContentInspectionRequired : Bool
    referencedContentInspectionRequiredIsTrue :
      referencedContentInspectionRequired ≡ true
    attributedSourceCreatesStatementTruth : Bool
    attributedSourceCreatesStatementTruthIsFalse :
      attributedSourceCreatesStatementTruth ≡ false

canonicalNativeReferenceAttributedSourceBoundary :
  NativeReferenceAttributedSourceBoundary
canonicalNativeReferenceAttributedSourceBoundary =
  native-reference-attributed-source-boundary true refl true refl true refl false refl
