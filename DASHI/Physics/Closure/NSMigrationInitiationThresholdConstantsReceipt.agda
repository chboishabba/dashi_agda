module DASHI.Physics.Closure.NSMigrationInitiationThresholdConstantsReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_+_; _≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Quantitative constant obligations for the live Sprint 147 gate.
--
-- This module does not prove MigrationInitiationThresholdForLargeData.
-- It records the normalized source-integral vs viscosity-suppression
-- constants and the exact inequality direction currently available:
--
--   sourceIntegralObserved <= sourceIntegralRequired
--   viscosityRetainedObserved <= viscosityRetainedRequired
--   baseline <= offAxisGainObserved
--   baseline <= logFeedbackObserved
--
-- The proof-bearing target directions needed for the live gate are therefore
-- intentionally false/open.

sourceIntegralObservedLowerBound : Nat
sourceIntegralObservedLowerBound = 82

sourceIntegralRequiredLowerBound : Nat
sourceIntegralRequiredLowerBound = sourceIntegralObservedLowerBound + 18

viscosityRetentionObservedLowerBound : Nat
viscosityRetentionObservedLowerBound = 46

viscosityRetentionRequiredLowerBound : Nat
viscosityRetentionRequiredLowerBound = viscosityRetentionObservedLowerBound + 54

normalizedBaselineUnit : Nat
normalizedBaselineUnit = 100

offAxisGainObservedUpperDemand : Nat
offAxisGainObservedUpperDemand = normalizedBaselineUnit + 34

logFeedbackObservedUpperDemand : Nat
logFeedbackObservedUpperDemand = normalizedBaselineUnit + 72

sourceIntegralBelowRequired :
  sourceIntegralObservedLowerBound ≤ sourceIntegralRequiredLowerBound
sourceIntegralBelowRequired = m≤m+n sourceIntegralObservedLowerBound 18

viscosityRetentionBelowRequired :
  viscosityRetentionObservedLowerBound ≤ viscosityRetentionRequiredLowerBound
viscosityRetentionBelowRequired = m≤m+n viscosityRetentionObservedLowerBound 54

offAxisGainExceedsBaseline :
  normalizedBaselineUnit ≤ offAxisGainObservedUpperDemand
offAxisGainExceedsBaseline = m≤m+n normalizedBaselineUnit 34

logFeedbackExceedsBaseline :
  normalizedBaselineUnit ≤ logFeedbackObservedUpperDemand
logFeedbackExceedsBaseline = m≤m+n normalizedBaselineUnit 72

sourceIntegralDominatesViscositySuppression : Bool
sourceIntegralDominatesViscositySuppression = false

viscositySuppressionUniformlyAbsorbed : Bool
viscositySuppressionUniformlyAbsorbed = false

offAxisGainUniformlyBounded : Bool
offAxisGainUniformlyBounded = false

logFeedbackUniformlyAbsorbed : Bool
logFeedbackUniformlyAbsorbed = false

quantitativeConstantsSufficientForMigrationInitiation : Bool
quantitativeConstantsSufficientForMigrationInitiation = false

quantitativeConstantsFailClosed : Bool
quantitativeConstantsFailClosed = true

data MigrationThresholdConstant : Set where
  sourceIntegralRequiredConstant :
    MigrationThresholdConstant

  sourceIntegralObservedConstant :
    MigrationThresholdConstant

  viscosityRetentionRequiredConstant :
    MigrationThresholdConstant

  viscosityRetentionObservedConstant :
    MigrationThresholdConstant

  offAxisGainDemandConstant :
    MigrationThresholdConstant

  logFeedbackDemandConstant :
    MigrationThresholdConstant

  normalizedBaselineConstant :
    MigrationThresholdConstant

canonicalMigrationThresholdConstants :
  List MigrationThresholdConstant
canonicalMigrationThresholdConstants =
  sourceIntegralRequiredConstant
  ∷ sourceIntegralObservedConstant
  ∷ viscosityRetentionRequiredConstant
  ∷ viscosityRetentionObservedConstant
  ∷ offAxisGainDemandConstant
  ∷ logFeedbackDemandConstant
  ∷ normalizedBaselineConstant
  ∷ []

migrationThresholdConstantCount : Nat
migrationThresholdConstantCount = 7

data MigrationThresholdRequiredEstimate : Set where
  proveSourceIntegralRequiredLowerBound :
    MigrationThresholdRequiredEstimate

  proveViscosityRetentionRequiredLowerBound :
    MigrationThresholdRequiredEstimate

  boundOffAxisGainByAbsorbableConstant :
    MigrationThresholdRequiredEstimate

  absorbLogFeedbackIntoViscousBudget :
    MigrationThresholdRequiredEstimate

  makeConstantsUniformAcrossLargeDataFamily :
    MigrationThresholdRequiredEstimate

canonicalMigrationThresholdRequiredEstimates :
  List MigrationThresholdRequiredEstimate
canonicalMigrationThresholdRequiredEstimates =
  proveSourceIntegralRequiredLowerBound
  ∷ proveViscosityRetentionRequiredLowerBound
  ∷ boundOffAxisGainByAbsorbableConstant
  ∷ absorbLogFeedbackIntoViscousBudget
  ∷ makeConstantsUniformAcrossLargeDataFamily
  ∷ []

migrationThresholdRequiredEstimateCount : Nat
migrationThresholdRequiredEstimateCount = 5

data MigrationThresholdInequalityDirection : Set where
  observedSourceBelowRequired :
    MigrationThresholdInequalityDirection

  observedViscosityBelowRequired :
    MigrationThresholdInequalityDirection

  adverseOffAxisGainAboveBaseline :
    MigrationThresholdInequalityDirection

  adverseLogFeedbackAboveBaseline :
    MigrationThresholdInequalityDirection

canonicalMigrationThresholdInequalityDirections :
  List MigrationThresholdInequalityDirection
canonicalMigrationThresholdInequalityDirections =
  observedSourceBelowRequired
  ∷ observedViscosityBelowRequired
  ∷ adverseOffAxisGainAboveBaseline
  ∷ adverseLogFeedbackAboveBaseline
  ∷ []

migrationThresholdInequalityDirectionCount : Nat
migrationThresholdInequalityDirectionCount = 4

data MigrationThresholdFailClosedFlag : Set where
  doNotReverseSourceIntegralInequality :
    MigrationThresholdFailClosedFlag

  doNotTreatSuppressedViscosityAsAbsorbing :
    MigrationThresholdFailClosedFlag

  doNotDropOffAxisGainDemand :
    MigrationThresholdFailClosedFlag

  doNotDropLogFeedbackDemand :
    MigrationThresholdFailClosedFlag

  doNotPromoteConstantsToMigrationThreshold :
    MigrationThresholdFailClosedFlag

canonicalMigrationThresholdFailClosedFlags :
  List MigrationThresholdFailClosedFlag
canonicalMigrationThresholdFailClosedFlags =
  doNotReverseSourceIntegralInequality
  ∷ doNotTreatSuppressedViscosityAsAbsorbing
  ∷ doNotDropOffAxisGainDemand
  ∷ doNotDropLogFeedbackDemand
  ∷ doNotPromoteConstantsToMigrationThreshold
  ∷ []

migrationThresholdFailClosedFlagCount : Nat
migrationThresholdFailClosedFlagCount = 5

inequalityDirectionString : String
inequalityDirectionString =
  "available directions: sourceIntegralObserved <= sourceIntegralRequired; viscosityRetainedObserved <= viscosityRetainedRequired; baseline <= offAxisGain; baseline <= logFeedback"

requiredEstimateString : String
requiredEstimateString =
  "required estimates: source integral lower bound, retained viscosity lower bound, off-axis gain absorption, log-feedback absorption, uniformity over the large-data family"

failClosedString : String
failClosedString =
  "quantitative constants are named but insufficient; MigrationInitiationThresholdForLargeData remains false/open"

record MigrationThresholdConstantObligationSurface : Set where
  constructor migrationThresholdConstantObligationSurface
  field
    inequalityDirections :
      String
    inequalityDirectionsCanonical :
      inequalityDirections ≡ inequalityDirectionString
    requiredEstimates :
      String
    requiredEstimatesCanonical :
      requiredEstimates ≡ requiredEstimateString
    failClosedBoundary :
      String
    failClosedBoundaryCanonical :
      failClosedBoundary ≡ failClosedString
    sourceBelowRequiredField :
      sourceIntegralObservedLowerBound ≤ sourceIntegralRequiredLowerBound
    viscosityBelowRequiredField :
      viscosityRetentionObservedLowerBound ≤ viscosityRetentionRequiredLowerBound
    offAxisAboveBaselineField :
      normalizedBaselineUnit ≤ offAxisGainObservedUpperDemand
    logFeedbackAboveBaselineField :
      normalizedBaselineUnit ≤ logFeedbackObservedUpperDemand
    sourceDominatesFalseField :
      sourceIntegralDominatesViscositySuppression ≡ false
    viscosityAbsorbedFalseField :
      viscositySuppressionUniformlyAbsorbed ≡ false
    constantsSufficientFalseField :
      quantitativeConstantsSufficientForMigrationInitiation ≡ false
    failClosedTrueField :
      quantitativeConstantsFailClosed ≡ true

open MigrationThresholdConstantObligationSurface public

canonicalMigrationThresholdConstantObligationSurface :
  MigrationThresholdConstantObligationSurface
canonicalMigrationThresholdConstantObligationSurface =
  migrationThresholdConstantObligationSurface
    inequalityDirectionString
    refl
    requiredEstimateString
    refl
    failClosedString
    refl
    sourceIntegralBelowRequired
    viscosityRetentionBelowRequired
    offAxisGainExceedsBaseline
    logFeedbackExceedsBaseline
    refl
    refl
    refl
    refl

data MigrationThresholdConstantPromotion : Set where

migrationThresholdConstantPromotionImpossibleHere :
  MigrationThresholdConstantPromotion →
  ⊥
migrationThresholdConstantPromotionImpossibleHere ()

record NSMigrationInitiationThresholdConstantsReceipt : Set where
  constructor nsMigrationInitiationThresholdConstantsReceipt
  field
    surface :
      MigrationThresholdConstantObligationSurface
    surfaceIsCanonical :
      surface ≡ canonicalMigrationThresholdConstantObligationSurface
    constants :
      List MigrationThresholdConstant
    constantsAreCanonical :
      constants ≡ canonicalMigrationThresholdConstants
    requiredEstimates :
      List MigrationThresholdRequiredEstimate
    requiredEstimatesAreCanonical :
      requiredEstimates ≡ canonicalMigrationThresholdRequiredEstimates
    inequalityDirections :
      List MigrationThresholdInequalityDirection
    inequalityDirectionsAreCanonical :
      inequalityDirections ≡ canonicalMigrationThresholdInequalityDirections
    failClosedFlags :
      List MigrationThresholdFailClosedFlag
    failClosedFlagsAreCanonical :
      failClosedFlags ≡ canonicalMigrationThresholdFailClosedFlags

open NSMigrationInitiationThresholdConstantsReceipt public

canonicalNSMigrationInitiationThresholdConstantsReceipt :
  NSMigrationInitiationThresholdConstantsReceipt
canonicalNSMigrationInitiationThresholdConstantsReceipt =
  nsMigrationInitiationThresholdConstantsReceipt
    canonicalMigrationThresholdConstantObligationSurface
    refl
    canonicalMigrationThresholdConstants
    refl
    canonicalMigrationThresholdRequiredEstimates
    refl
    canonicalMigrationThresholdInequalityDirections
    refl
    canonicalMigrationThresholdFailClosedFlags
    refl

migrationThresholdConstantCountPackage :
  (migrationThresholdConstantCount ≡ 7)
  × (migrationThresholdRequiredEstimateCount ≡ 5)
  × (migrationThresholdInequalityDirectionCount ≡ 4)
  × (migrationThresholdFailClosedFlagCount ≡ 5)
migrationThresholdConstantCountPackage =
  refl , refl , refl , refl

migrationThresholdConstantFailClosedPackage :
  (sourceIntegralDominatesViscositySuppression ≡ false)
  × (viscositySuppressionUniformlyAbsorbed ≡ false)
  × (offAxisGainUniformlyBounded ≡ false)
  × (logFeedbackUniformlyAbsorbed ≡ false)
  × (quantitativeConstantsSufficientForMigrationInitiation ≡ false)
  × (quantitativeConstantsFailClosed ≡ true)
migrationThresholdConstantFailClosedPackage =
  refl , refl , refl , refl , refl , refl

migrationThresholdConstantReceiptPackage :
  MigrationThresholdConstantObligationSurface
  × NSMigrationInitiationThresholdConstantsReceipt
migrationThresholdConstantReceiptPackage =
  canonicalMigrationThresholdConstantObligationSurface ,
  canonicalNSMigrationInitiationThresholdConstantsReceipt
