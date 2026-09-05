module DASHI.Physics.Nuclear.LeBlancSensorQualificationMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- NASA FSP I&C source-shaped qualification matrix.

data QualificationAxis : Set where
  temperature neutronFlux neutronFluence gammaDose pressure massFlow vibration lifetime autonomy : QualificationAxis

data QualificationEvidence : Set where
  literatureOnly databaseEntry benchTest acceleratedTest radiationTest integratedSubsystemTest flightLikeDemonstration : QualificationEvidence

data QualificationState : Set where uninspected candidate screened qualifiedForEnvelope integrated : QualificationState

record SensorQualificationCell : Set where
  constructor sensor-qualification-cell
  field
    sensorLabel : String
    axis : QualificationAxis
    requiredEnvelope : String
    demonstratedEnvelope : String
    evidence : QualificationEvidence
    state : QualificationState
    provenance : String

open SensorQualificationCell public

record ReliabilityReceipt : Set where
  constructor reliability-receipt
  field
    sensorLabel : String
    missionDuration : String
    environment : String
    failureProbabilityModel : String
    acceleratedTestMapping : String
    physicsOfFailureModel : String
    sourceReference : String

open ReliabilityReceipt public

record QualificationPromotion : Set where
  constructor qualification-promotion
  field
    requirementReceipt : SensorQualificationCell
    reliabilityReceipt : ReliabilityReceipt
    integratedFaultSemantics : String
    correctiveActionPolicy : String
    measurementIntegrityChecked : Bool
    measurementIntegrityCheckedIsTrue : measurementIntegrityChecked ≡ true

open QualificationPromotion public

record LeBlancQualificationBoundary : Set where
  constructor leblanc-qualification-boundary
  field
    literatureEntryEqualsQualification : Bool
    literatureEntryEqualsQualificationIsFalse : literatureEntryEqualsQualification ≡ false
    acceleratedTestAloneDefinesTenYearFailureProbability : Bool
    acceleratedTestAloneDefinesTenYearFailureProbabilityIsFalse :
      acceleratedTestAloneDefinesTenYearFailureProbability ≡ false
    componentQualificationEqualsIntegratedAutonomy : Bool
    componentQualificationEqualsIntegratedAutonomyIsFalse : componentQualificationEqualsIntegratedAutonomy ≡ false
    qualificationMustTraceToRequirementEnvelope : Bool
    qualificationMustTraceToRequirementEnvelopeIsTrue : qualificationMustTraceToRequirementEnvelope ≡ true
    autonomyNeedsFaultSemanticsAndPolicy : Bool
    autonomyNeedsFaultSemanticsAndPolicyIsTrue : autonomyNeedsFaultSemanticsAndPolicy ≡ true

canonicalLeBlancQualificationBoundary : LeBlancQualificationBoundary
canonicalLeBlancQualificationBoundary =
  leblanc-qualification-boundary false refl false refl false refl true refl true refl
