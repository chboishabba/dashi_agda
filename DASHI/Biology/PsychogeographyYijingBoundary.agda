module DASHI.Biology.PsychogeographyYijingBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record PsychogeographyYijingAuthorityBoundary : Set where
  constructor psychogeographyYijingAuthorityBoundary
  field
    psychogeographyIsPrimaryOrganisingFrame : Bool
    psychogeographyIsPrimaryOrganisingFrameIsTrue :
      psychogeographyIsPrimaryOrganisingFrame ≡ true
    hexagramIsCoarseContextIndexedObservation : Bool
    hexagramIsCoarseContextIndexedObservationIsTrue :
      hexagramIsCoarseContextIndexedObservation ≡ true
    castEntailsExternalPrediction : Bool
    castEntailsExternalPredictionIsFalse :
      castEntailsExternalPrediction ≡ false
    associationIsRecoveredMemoryAuthority : Bool
    associationIsRecoveredMemoryAuthorityIsFalse :
      associationIsRecoveredMemoryAuthority ≡ false
    zeroTritDiagnosesDissociation : Bool
    zeroTritDiagnosesDissociationIsFalse :
      zeroTritDiagnosesDissociation ≡ false
    obstructionDiagnosesTrauma : Bool
    obstructionDiagnosesTraumaIsFalse : obstructionDiagnosesTrauma ≡ false
    fictionalPaleIsPhysicalCosmology : Bool
    fictionalPaleIsPhysicalCosmologyIsFalse :
      fictionalPaleIsPhysicalCosmology ≡ false
    cityLiterallyThinksClaimed : Bool
    cityLiterallyThinksClaimedIsFalse : cityLiterallyThinksClaimed ≡ false
    finitePathsAreContinuumUrbanDynamics : Bool
    finitePathsAreContinuumUrbanDynamicsIsFalse :
      finitePathsAreContinuumUrbanDynamics ≡ false
    nonErasingReorganisationAvailable : Bool
    nonErasingReorganisationAvailableIsTrue :
      nonErasingReorganisationAvailable ≡ true
    boundaryNote : String

canonicalPsychogeographyYijingAuthorityBoundary :
  PsychogeographyYijingAuthorityBoundary
canonicalPsychogeographyYijingAuthorityBoundary =
  psychogeographyYijingAuthorityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Psychogeography is the organising frame: paths through spatial-social relations transform memory, attention and action. Yijing, trauma and Disco-derived structures are bounded observation and transition interfaces, not predictive, diagnostic or physical authorities."
