module DASHI.Law.ReviewedTreatmentBundleSemanticDedupExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Reviewed-treatment evidence multiplicity is not semantic-hop multiplicity.
--
-- Doueihi paragraphs 357 and 435 are distinct reviewed source units.  Both can
-- support the same source→target Supports edge.  The graph therefore gains one
-- semantic treatment edge while retaining both provenance units.
------------------------------------------------------------------------

data ReviewUnit : Set where
  paragraph357 : ReviewUnit
  paragraph435 : ReviewUnit

data SemanticTreatmentEdge : Set where
  doueihiSupportsGiumelli : SemanticTreatmentEdge

edgeFor : ReviewUnit → SemanticTreatmentEdge
edgeFor paragraph357 = doueihiSupportsGiumelli
edgeFor paragraph435 = doueihiSupportsGiumelli

corroboratingUnitsHaveSameSemanticEdge :
  edgeFor paragraph357 ≡ edgeFor paragraph435
corroboratingUnitsHaveSameSemanticEdge = refl

record ReviewedTreatmentBundleBoundary : Set where
  constructor reviewedTreatmentBundleBoundary
  field
    twoReviewedUnitsMaySupportOneSemanticEdge : Bool
    twoReviewedUnitsMaySupportOneSemanticEdgeIsTrue :
      twoReviewedUnitsMaySupportOneSemanticEdge ≡ true

    semanticHopCountMustEqualEvidenceUnitCount : Bool
    semanticHopCountMustEqualEvidenceUnitCountIsFalse :
      semanticHopCountMustEqualEvidenceUnitCount ≡ false

    allSupportingReviewUnitProvenanceRetained : Bool
    allSupportingReviewUnitProvenanceRetainedIsTrue :
      allSupportingReviewUnitProvenanceRetained ≡ true

    deduplicationMayDiscardUnsupportedResiduals : Bool
    deduplicationMayDiscardUnsupportedResidualsIsFalse :
      deduplicationMayDiscardUnsupportedResiduals ≡ false

    bundledTreatmentCreatesLegalAuthority : Bool
    bundledTreatmentCreatesLegalAuthorityIsFalse :
      bundledTreatmentCreatesLegalAuthority ≡ false

open ReviewedTreatmentBundleBoundary public

canonicalReviewedTreatmentBundleBoundary :
  ReviewedTreatmentBundleBoundary
canonicalReviewedTreatmentBundleBoundary =
  reviewedTreatmentBundleBoundary
    true refl
    false refl
    true refl
    false refl
    false refl

data EvidenceMultiplicityAutomaticallySemanticMultiplicity : Set where
data SemanticDedupMayDropResiduals : Set where
data BundledTreatmentAutomaticallyAuthority : Set where

evidenceMultiplicityDoesNotForceSemanticMultiplicity :
  EvidenceMultiplicityAutomaticallySemanticMultiplicity → ⊥
evidenceMultiplicityDoesNotForceSemanticMultiplicity ()

semanticDedupCannotDropResiduals :
  SemanticDedupMayDropResiduals → ⊥
semanticDedupCannotDropResiduals ()

bundledTreatmentDoesNotCreateAuthority :
  BundledTreatmentAutomaticallyAuthority → ⊥
bundledTreatmentDoesNotCreateAuthority ()
