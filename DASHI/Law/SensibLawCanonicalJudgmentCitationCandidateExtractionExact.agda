module DASHI.Law.SensibLawCanonicalJudgmentCitationCandidateExtractionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Rust-led parity owner for pre-review judgment extraction.
--
-- Canonical judgment text may expose paragraph-located citation-shaped strings
-- and lexical treatment hints.  These are observations/candidates only.  They do
-- not become proposition correspondence, CitationUse, ReasoningRole, ratio,
-- current authority, applicability or truth until the ordinary reviewed source
-- diligence/reasoning path pays those coordinates.
------------------------------------------------------------------------

rustRepository : String
rustRepository = "chboishabba/slr"

rustBranch : String
rustBranch = "agent/governed-online-r6-v2"

rustSourceHead : String
rustSourceHead = "7364015e76ebf891f4fe1cd9958af18f57c378e3"

record CanonicalJudgmentCitationCandidateBoundary : Set where
  constructor canonicalJudgmentCitationCandidateBoundary
  field
    documentIdentityRetained : Bool
    documentIdentityRetainedIsTrue : documentIdentityRetained ≡ true

    sourceRevisionRetained : Bool
    sourceRevisionRetainedIsTrue : sourceRevisionRetained ≡ true

    canonicalTextDigestRetained : Bool
    canonicalTextDigestRetainedIsTrue : canonicalTextDigestRetained ≡ true

    stableParagraphOrdinalRetained : Bool
    stableParagraphOrdinalRetainedIsTrue : stableParagraphOrdinalRetained ≡ true

    stableParagraphLocatorRetained : Bool
    stableParagraphLocatorRetainedIsTrue : stableParagraphLocatorRetained ≡ true

    reportedParagraphLabelMayBeRetained : Bool
    reportedParagraphLabelMayBeRetainedIsTrue : reportedParagraphLabelMayBeRetained ≡ true

    mediumNeutralCitationShapeMayBeExtracted : Bool
    mediumNeutralCitationShapeMayBeExtractedIsTrue :
      mediumNeutralCitationShapeMayBeExtracted ≡ true

    lexicalTreatmentHintsMayBeExtracted : Bool
    lexicalTreatmentHintsMayBeExtractedIsTrue :
      lexicalTreatmentHintsMayBeExtracted ≡ true

    extractionCandidateOnly : Bool
    extractionCandidateOnlyIsTrue : extractionCandidateOnly ≡ true

    extractionInitiallyReviewed : Bool
    extractionInitiallyReviewedIsFalse : extractionInitiallyReviewed ≡ false

    citationShapeAutomaticallySemanticCorrespondence : Bool
    citationShapeAutomaticallySemanticCorrespondenceIsFalse :
      citationShapeAutomaticallySemanticCorrespondence ≡ false

    lexicalTreatmentHintAutomaticallyCitationUse : Bool
    lexicalTreatmentHintAutomaticallyCitationUseIsFalse :
      lexicalTreatmentHintAutomaticallyCitationUse ≡ false

    citationCandidateAutomaticallyCurrentAuthority : Bool
    citationCandidateAutomaticallyCurrentAuthorityIsFalse :
      citationCandidateAutomaticallyCurrentAuthority ≡ false

canonicalCanonicalJudgmentCitationCandidateBoundary :
  CanonicalJudgmentCitationCandidateBoundary
canonicalCanonicalJudgmentCitationCandidateBoundary =
  canonicalJudgmentCitationCandidateBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Fail-closed observation/promotion firewalls.
------------------------------------------------------------------------

data CitationShapeAutomaticallyTreatmentEdge : Set where
data TreatmentWordAutomaticallyAppliedUse : Set where
data CandidateLocatorAutomaticallyRatio : Set where

data ExtractionAutomaticallyConsumerClosure : Set where

citationShapeDoesNotBecomeTreatmentEdge :
  CitationShapeAutomaticallyTreatmentEdge → ⊥
citationShapeDoesNotBecomeTreatmentEdge ()

treatmentWordDoesNotBecomeAppliedUse :
  TreatmentWordAutomaticallyAppliedUse → ⊥
treatmentWordDoesNotBecomeAppliedUse ()

candidateLocatorDoesNotBecomeRatio :
  CandidateLocatorAutomaticallyRatio → ⊥
candidateLocatorDoesNotBecomeRatio ()

extractionDoesNotBecomeConsumerClosure :
  ExtractionAutomaticallyConsumerClosure → ⊥
extractionDoesNotBecomeConsumerClosure ()
