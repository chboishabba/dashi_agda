module DASHI.Physics.Nuclear.FissionICQualificationReliabilityDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Generic fission instrumentation/control qualification owner.
-- Sources:
-- NASA Glenn, "NASA Fission Instrumentation and Controls Workshop" (2024), stable NASA page.
-- NASA, "NASA 40 kW Fission Surface Power", NTRS 20250008475 (2025).

data QualificationAxis : Set where
  neutronFluence
  gammaDose
  temperatureRange
  missionLifetime
  measurementIntegrity
  probabilityOfFailure
  acceleratedLifeTest
  physicsOfFailureModel
  autonomousFaultDetection
  autonomousControlResponse
  communicationReliability
  calibrationDrift
  : QualificationAxis

record QualificationEnvelope : Set where
  constructor qualification-envelope
  field
    axes : List QualificationAxis
    neutronRange : String
    gammaRange : String
    temperatureRangeText : String
    operationalLife : String
    sourceReference : String
    boundedReading : String

open QualificationEnvelope public

canonicalQualificationEnvelope : QualificationEnvelope
canonicalQualificationEnvelope = qualification-envelope
  (neutronFluence ∷ gammaDose ∷ temperatureRange ∷ missionLifetime ∷ measurementIntegrity ∷ probabilityOfFailure ∷ acceleratedLifeTest ∷ physicsOfFailureModel ∷ autonomousFaultDetection ∷ autonomousControlResponse ∷ calibrationDrift ∷ [])
  "NASA maturation material gives approximately 10^12 to 10^21 n cm^-2 as a programme-level neutron-fluence range"
  "NASA maturation material gives programme-level gamma exposure spanning roughly 30 krad to 8x10^10 krad(Si)"
  "approximately 350-1250 K programme-level range"
  "10-year FSP operation"
  "NASA NTRS 20250008475; NASA Glenn 2024 FICS Workshop"
  "These are programme-level maturation drivers, not a statement that every component sees every extreme simultaneously."

record ReliabilityLogic : Set where
  constructor reliability-logic
  field
    noMaintenanceOrReplacement : Bool
    noMaintenanceOrReplacementIsTrue : noMaintenanceOrReplacement ≡ true
    autonomousDiagnosisRequired : Bool
    autonomousDiagnosisRequiredIsTrue : autonomousDiagnosisRequired ≡ true
    offNormalAutomatedResponseDesired : Bool
    offNormalAutomatedResponseDesiredIsTrue : offNormalAutomatedResponseDesired ≡ true
    qualificationRequiresProbabilityOfFailureReasoning : Bool
    qualificationRequiresProbabilityOfFailureReasoningIsTrue : qualificationRequiresProbabilityOfFailureReasoning ≡ true

canonicalReliabilityLogic : ReliabilityLogic
canonicalReliabilityLogic = reliability-logic true refl true refl true refl true refl

record QualificationBoundary : Set where
  constructor qualification-boundary
  field
    radiationHardImpliesMissionQualified : Bool
    radiationHardImpliesMissionQualifiedIsFalse : radiationHardImpliesMissionQualified ≡ false
    thermalSurvivalImpliesMeasurementIntegrity : Bool
    thermalSurvivalImpliesMeasurementIntegrityIsFalse : thermalSurvivalImpliesMeasurementIntegrity ≡ false
    singleEnvironmentTestImpliesCombinedEnvironmentReliability : Bool
    singleEnvironmentTestImpliesCombinedEnvironmentReliabilityIsFalse : singleEnvironmentTestImpliesCombinedEnvironmentReliability ≡ false
    componentReliabilityImpliesClosedLoopFaultTolerance : Bool
    componentReliabilityImpliesClosedLoopFaultToleranceIsFalse : componentReliabilityImpliesClosedLoopFaultTolerance ≡ false

canonicalQualificationBoundary : QualificationBoundary
canonicalQualificationBoundary = qualification-boundary false refl false refl false refl false refl

data QualificationReverseTarget : Set where
  acquireComponentSpecificDoseTemperatureEnvelope
  acquireCalibrationDriftCurve
  acquireAcceleratedLifeModel
  acquirePhysicsOfFailureParameters
  acquireCombinedEnvironmentTest
  acquireFaultInjectionResults
  acquireSystemLevelFailureProbability
  acquireAutonomousRecoveryDemonstration
  : QualificationReverseTarget
