module DASHI.Ontology.EducationOntologyMappingPNFValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_)

import DASHI.Cognition.PNF.TypePressure as PNFPressure
open import DASHI.Ontology.EducationOntologyMappingPNFExact
open import DASHI.Ontology.EducationOntologyMappingSSSOMExact

samplePressureInterpretation : MappingPNFInterpretation sampleManualExactMapping
samplePressureInterpretation =
  mappingPNFInterpretation (+ 1) "reviewed curator evidence" "sample mapping set"

adapterPreservesMappingEvidence :
  PNFPressure.evidence (asTypePressureContribution samplePressureInterpretation)
  ≡ sampleManualExactMapping
adapterPreservesMappingEvidence = refl

adapterPreservesSignedPressure :
  PNFPressure.signedPressure (asTypePressureContribution samplePressureInterpretation)
  ≡ + 1
adapterPreservesSignedPressure = refl

mappingPredicateDoesNotDeterminePressure :
  MappingPredicateDeterminesPressure → ⊥
mappingPredicateDoesNotDeterminePressure = predicateDoesNotDeterminePressure

mappingConfidenceDoesNotDeterminePressure :
  MappingConfidenceDeterminesPressure → ⊥
mappingConfidenceDoesNotDeterminePressure = confidenceDoesNotDeterminePressure

mappingPressureCannotAssertType :
  PNFPressure.TypePressurePromotionPermission → ⊥
mappingPressureCannotAssertType = PNFPressure.pressureAloneCannotAssertType

mappingRowCannotAssertOntologyTruth :
  MappingTruthPermission mappingForReviewOnly → ⊥
mappingRowCannotAssertOntologyTruth = mappingCannotAssertOntologyTruth

reviewFindingCanRemainResidual :
  mappingFindingToResidual unresolvedMappingConflict ≡ openResidual
reviewFindingCanRemainResidual = refl
