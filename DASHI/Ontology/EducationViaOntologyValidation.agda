module DASHI.Ontology.EducationViaOntologyValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)
open import Data.Empty using (⊥)

open import DASHI.Ontology.EducationViaOntologyExact

------------------------------------------------------------------------
-- TDD contract: this file is committed before the production owner.
-- It pins the non-collapse and attribution boundaries required by the
-- Mkrtchyan education-via-ontology tranche.
------------------------------------------------------------------------

redMeansTitleResolutionGap :
  observedGapKind apparentlyMissingRed ≡ titleResolutionGap
redMeansTitleResolutionGap = refl

redDoesNotMeanKnowledgeGap :
  observedGapKind apparentlyMissingRed ≡ knowledgeGap → ⊥
redDoesNotMeanKnowledgeGap ()

articleGapDoesNotMeanConceptGap : articleGap ≡ conceptGap → ⊥
articleGapDoesNotMeanConceptGap ()

conceptGapDoesNotMeanKnowledgeGap : conceptGap ≡ knowledgeGap → ⊥
conceptGapDoesNotMeanKnowledgeGap ()

candidateContributionHasNoTruthPermission :
  OntologyTruthPermission contributionForReview → ⊥
candidateContributionHasNoTruthPermission = candidateCannotAssertOntologyTruth

sourceClaimsDoNotBecomeRepoTheorems :
  SourceClaimPromotionPermission sourceClaimOnly → ⊥
sourceClaimsDoNotBecomeRepoTheorems = sourceClaimCannotPromoteItself

canonicalStatusPinsAttributionBoundary :
  sourceClaimsAreBounded canonicalEducationViaOntologyStatus ≡ true
canonicalStatusPinsAttributionBoundary = sourceClaimsAreBoundedIsTrue canonicalEducationViaOntologyStatus

canonicalStatusPinsTreeProjectionBoundary :
  ontologyTreeIsProjection canonicalEducationViaOntologyStatus ≡ true
canonicalStatusPinsTreeProjectionBoundary = ontologyTreeIsProjectionIsTrue canonicalEducationViaOntologyStatus

canonicalStatusPinsGapNonCollapse :
  gapKindsRemainDistinct canonicalEducationViaOntologyStatus ≡ true
canonicalStatusPinsGapNonCollapse = gapKindsRemainDistinctIsTrue canonicalEducationViaOntologyStatus

canonicalStatusPinsContributionReviewBoundary :
  contributionsRequireReview canonicalEducationViaOntologyStatus ≡ true
canonicalStatusPinsContributionReviewBoundary = contributionsRequireReviewIsTrue canonicalEducationViaOntologyStatus
