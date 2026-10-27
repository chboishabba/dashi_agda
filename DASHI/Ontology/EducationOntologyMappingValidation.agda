module DASHI.Ontology.EducationOntologyMappingValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Ontology.EducationOntologyMappingSSSOMExact

------------------------------------------------------------------------
-- TDD contract for the education/ontology-mapping continuation.
--
-- This validation owner is committed before the production owner.  It pins
-- the core non-collapse obligations introduced by SSSOM/lgbtDB-style mapping
-- governance and the existing DASHI/SensibLaw repair boundaries.
------------------------------------------------------------------------

exactMatchIsNotOwlEquivalentClass :
  skosExactMatch ≡ owlEquivalentClass → ⊥
exactMatchIsNotOwlEquivalentClass ()

broadMatchIsNotExactMatch :
  skosBroadMatch ≡ skosExactMatch → ⊥
broadMatchIsNotExactMatch ()

mappingRecordCannotAssertOntologyTruth :
  MappingTruthPermission mappingForReviewOnly → ⊥
mappingRecordCannotAssertOntologyTruth = mappingCannotAssertOntologyTruth

reviewedMappingStillNeedsInferenceProfile :
  MappingInferencePromotionPermission reviewedMapping → ⊥
reviewedMappingStillNeedsInferenceProfile = reviewedMappingCannotPromoteAllInferenceLanguages

subclassSafetyDoesNotImplyDisjointnessSafety :
  subclassOnlySafeForSubclass ≡ true →
  subclassOnlySafeForDisjointness ≡ true → ⊥
subclassSafetyDoesNotImplyDisjointnessSafety _ ()

confidenceDoesNotRewritePredicate :
  mappingPredicate sampleManualExactMapping ≡ skosExactMatch
confidenceDoesNotRewritePredicate = refl

mappingSetPreservesLicense :
  mappingSetLicense sampleMappingSet ≡ "CC-BY-4.0"
mappingSetPreservesLicense = refl

canonicalStatusPinsPredicateNonCollapse :
  predicateKindsRemainDistinct canonicalMappingGovernanceStatus ≡ true
canonicalStatusPinsPredicateNonCollapse =
  predicateKindsRemainDistinctIsTrue canonicalMappingGovernanceStatus

canonicalStatusPinsRepairBoundary :
  mappingRepairRequiresReview canonicalMappingGovernanceStatus ≡ true
canonicalStatusPinsRepairBoundary =
  mappingRepairRequiresReviewIsTrue canonicalMappingGovernanceStatus

canonicalStatusPinsRosarioAttributionBoundary :
  rosarioIsPriorArtNotRepoIdentity canonicalMappingGovernanceStatus ≡ true
canonicalStatusPinsRosarioAttributionBoundary =
  rosarioIsPriorArtNotRepoIdentityIsTrue canonicalMappingGovernanceStatus
