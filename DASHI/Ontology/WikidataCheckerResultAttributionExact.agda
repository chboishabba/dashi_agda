module DASHI.Ontology.WikidataCheckerResultAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- A Boolean-ish checker surface cannot identify why a diagnostic failed.
-- Failure may be target-local, source-local, alignment-local, acquisition-local
-- or merely unresolved.  The detailed attribution fibre must be retained.
------------------------------------------------------------------------

data DiagnosticOrigin : Set where
  sourceFailure : DiagnosticOrigin
  transcriptionFailure : DiagnosticOrigin
  alignmentFailure : DiagnosticOrigin
  targetGraphFailure : DiagnosticOrigin
  missingRequiredEvidence : DiagnosticOrigin
  noFailure : DiagnosticOrigin

checkerBit : DiagnosticOrigin → Bool
checkerBit noFailure = true
checkerBit _ = false

sourceAndAlignmentShareFailBit :
  checkerBit sourceFailure ≡ checkerBit alignmentFailure
sourceAndAlignmentShareFailBit = refl

targetAndMissingShareFailBit :
  checkerBit targetGraphFailure ≡ checkerBit missingRequiredEvidence
targetAndMissingShareFailBit = refl

sourceIsNotAlignment : sourceFailure ≡ alignmentFailure → ⊥
sourceIsNotAlignment ()

targetIsNotMissing : targetGraphFailure ≡ missingRequiredEvidence → ⊥
targetIsNotMissing ()

record ExactCheckerOriginDecoder : Set where
  constructor exactCheckerOriginDecoder
  field
    decode : Bool → DiagnosticOrigin
    exact : (origin : DiagnosticOrigin) → decode (checkerBit origin) ≡ origin

open ExactCheckerOriginDecoder public

noExactCheckerOriginDecoder : ExactCheckerOriginDecoder → ⊥
noExactCheckerOriginDecoder decoder =
  sourceIsNotAlignment
    (trans
      (sym (exact decoder sourceFailure))
      (exact decoder alignmentFailure))

checkerFalseDoesNotIdentifyTargetGraphFailure :
  checkerBit targetGraphFailure ≡ false
checkerFalseDoesNotIdentifyTargetGraphFailure = refl

checkerFalseAlsoOccursForMissingEvidence :
  checkerBit missingRequiredEvidence ≡ false
checkerFalseAlsoOccursForMissingEvidence = refl

record CheckerAttributionBoundary : Set where
  constructor checkerAttributionBoundary
  field
    passFailSurfaceIsUseful : Bool
    failBitIdentifiesFailureLayer : Bool
    missingEvidenceEqualsTargetRefutation : Bool
    detailedAttributionMustSurviveForDiagnosis : Bool

canonicalCheckerAttributionBoundary : CheckerAttributionBoundary
canonicalCheckerAttributionBoundary =
  checkerAttributionBoundary true false false true
