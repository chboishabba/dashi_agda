module DASHI.Ontology.OntologyRepairPluralityMaxCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (+_; -[1+_])

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
