module DASHI.Ontology.OntologyRepairPluralityMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
open import DASHI.Ontology.EducationOntologyMappingSSSOMExact
open import DASHI.Ontology.OntologyRepairPluralityMaxCutExact

predicateTooStrongRoutesToUnderspecification :
  suggestedOperation predicateTooStrong ≡ Repair.underspecifyType
predicateTooStrongRoutesToUnderspecification = refl

versionDriftRoutesToReview :
  suggestedOperation sourceVersionDrift ≡ Repair.holdForReview
versionDriftRoutesToReview = refl

disjointnessConflictRoutesToReview :
  suggestedOperation disjointnessConflict ≡ Repair.holdForReview
disjointnessConflictRoutesToReview = refl

compiledSuggestionPreservesRoutedOperation :
  (target : Repair.RepairTarget) →
  (evidence : Repair.RepairEvidence) →
  Repair.operation (compileRepairSuggestion target predicateTooStrong evidence)
  ≡ Repair.underspecifyType
compiledSuggestionPreservesRoutedOperation target evidence = refl

pluralPressureCannotAssertTruth :
  PluralPressureTruthPermission → ⊥
pluralPressureCannotAssertTruth = pluralPressureCannotPromoteTruth

suggestedRepairCannotAuthorizeMutation :
  SuggestedRepairMutationPermission → ⊥
suggestedRepairCannotAuthorizeMutation = suggestionCannotAuthorizeMutation

versionDriftDoesNotRefuteMapping :
  VersionDriftRefutationPermission → ⊥
versionDriftDoesNotRefuteMapping = driftCannotRefuteMapping

coreProjectionRoundTrips :
  decodeCoreMapping (encodeCoreMapping sampleManualExactMapping) ≡ sampleManualExactMapping
coreProjectionRoundTrips = decodeEncodeCoreMapping sampleManualExactMapping
