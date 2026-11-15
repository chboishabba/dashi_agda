module DASHI.Biology.KitzerowBH4EvidenceRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.KitzerowBH4EvidenceAtlasExact as Atlas
import DASHI.Biology.KitzerowPriorityGenealogyExact as Priority

------------------------------------------------------------------------
-- Regression witnesses: the evidence dimensions must remain non-collapsing.
------------------------------------------------------------------------

supportDoesNotImplyPriority :
  Priority.priorityCoordinate Priority.supportWithoutPriority ≡ Atlas.priorArtBeforeKitzerow
supportDoesNotImplyPriority = refl

priorityDoesNotImplyContact :
  Priority.contactCoordinate Priority.priorityWithoutContact ≡ Atlas.noContactEvidenceAcquired
priorityDoesNotImplyContact = refl

contactDoesNotImplyArticleCitation :
  Priority.GenealogyBoundary.contactImpliesArticleCitation Priority.canonicalGenealogyBoundary ≡ false
contactDoesNotImplyArticleCitation = refl

contactDoesNotImplyPlagiarism :
  Priority.AttributionAssessment.plagiarismProven Priority.stanfordAssessment ≡ false
contactDoesNotImplyPlagiarism = refl

nodeSupportDoesNotConfirmWholeGraph :
  Atlas.wholeModelConfirmed Atlas.ojhaNOToTSC2ToMTOR ≡ false
nodeSupportDoesNotConfirmWholeGraph = refl

stanfordContactRemainsUnverifiedPrimary :
  Priority.verifiedPrimaryContact Priority.stanfordContactEvidence ≡ false
stanfordContactRemainsUnverifiedPrimary = refl

stanfordArticleRemainsUncitedInAcquiredText :
  Priority.publicationReferenceStatus Priority.stanford2025ReferenceEvidence ≡ Priority.kitzerowNotFoundInArticleText
stanfordArticleRemainsUncitedInAcquiredText = refl

brazilReviewDoesNotConfirmWholeGraph :
  Atlas.wholeModelConfirmed Atlas.brazilBH4Review ≡ false
brazilReviewDoesNotConfirmWholeGraph = refl

naviauxOverlapDoesNotProvePlagiarism :
  Priority.AttributionAssessment.plagiarismProven Priority.naviauxAssessment ≡ false
naviauxOverlapDoesNotProvePlagiarism = refl

princetonComplaintDoesNotProvePlagiarism :
  Priority.AttributionAssessment.plagiarismProven Priority.princetonAssessment ≡ false
princetonComplaintDoesNotProvePlagiarism = refl

priorArtSubtractionIsRequired :
  Atlas.AtlasBoundary.priorArtSubtractedBeforeNoveltyClaim Atlas.canonicalAtlasBoundary ≡ true
priorArtSubtractionIsRequired = refl
