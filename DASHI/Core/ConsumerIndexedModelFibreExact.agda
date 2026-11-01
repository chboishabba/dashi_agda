module DASHI.Core.ConsumerIndexedModelFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CONSUMER-INDEXED MODEL FIBRE
--
-- DASHI-original generic machinery.
--
-- A model is not represented as one unindexed function.  It is carried over a
-- declared context/site, spatial scale, temporal window, intervention and
-- consumer/question.  Adequacy is therefore proposition-indexed by the
-- consumer, rather than promoted globally from the mere existence of outputs.
------------------------------------------------------------------------

record ModelIndex : Set₁ where
  constructor model-index
  field
    Context SpatialScale TemporalWindow Intervention ConsumerQuestion : Set
    context : Context
    spatialScale : SpatialScale
    temporalWindow : TemporalWindow
    intervention : Intervention
    consumerQuestion : ConsumerQuestion
    purposeReference : String

open ModelIndex public

record ModelFibre (index : ModelIndex) : Set₁ where
  constructor model-fibre
  field
    StateCarrier ObservationCarrier InterventionCarrier ParameterCarrier : Set
    stateReference : String
    observationReference : String
    interventionReference : String
    parameterReference : String

    Dynamics : StateCarrier → InterventionCarrier → ParameterCarrier → StateCarrier
    Observe : StateCarrier → ObservationCarrier

    CalibrationReceipt InitialConditionReceipt BoundaryConditionReceipt
      UncertaintyCarrier ValidationReceipt CounterfactualReceipt : Set

    calibrationReceipt : CalibrationReceipt
    initialConditionReceipt : InitialConditionReceipt
    boundaryConditionReceipt : BoundaryConditionReceipt
    uncertaintyCarrier : UncertaintyCarrier
    validationReceipt : ValidationReceipt
    counterfactualReceipt : CounterfactualReceipt

    AdequacyForDeclaredConsumer : Set
    adequacyForDeclaredConsumer : AdequacyForDeclaredConsumer

open ModelFibre public

------------------------------------------------------------------------
-- A reproducible model fibre receipt does not become a universal adequacy
-- certificate.  Any consumer transfer requires an explicit bridge.
------------------------------------------------------------------------

data DeclaredConsumerAdequacyImpliesOtherConsumerAdequacyPermission : Set where

data ModelOutputImpliesGlobalAdequacyPermission : Set where

data ValidationReceiptImpliesEveryUseAdequatePermission : Set where

declaredConsumerAdequacyDoesNotAutoTransfer :
  DeclaredConsumerAdequacyImpliesOtherConsumerAdequacyPermission → ⊥
declaredConsumerAdequacyDoesNotAutoTransfer ()

modelOutputDoesNotAutoPromoteToGlobalAdequacy :
  ModelOutputImpliesGlobalAdequacyPermission → ⊥
modelOutputDoesNotAutoPromoteToGlobalAdequacy ()

validationDoesNotAutoPromoteToEveryUse :
  ValidationReceiptImpliesEveryUseAdequatePermission → ⊥
validationDoesNotAutoPromoteToEveryUse ()

------------------------------------------------------------------------
-- Separate execution from empirical truth.
------------------------------------------------------------------------

record SimulationReceipt : Set₁ where
  constructor simulation-receipt
  field
    ModelVersion InputVersion ParameterVersion SolverVersion Output Diagnostics : Set
    modelVersion : ModelVersion
    inputVersion : InputVersion
    parameterVersion : ParameterVersion
    solverVersion : SolverVersion
    output : Output
    diagnostics : Diagnostics
    modelVersionReference : String
    inputVersionReference : String
    parameterVersionReference : String
    solverReference : String

open SimulationReceipt public

record EmpiricalValidationReceipt : Set₁ where
  constructor empirical-validation-receipt
  field
    Prediction Observation ComparisonCriterion : Set
    prediction : Prediction
    observation : Observation
    comparisonCriterion : ComparisonCriterion
    validationReference : String

open EmpiricalValidationReceipt public

data SimulationReceiptImpliesEmpiricalTruthPermission : Set where

data ReproducibilityImpliesEmpiricalAccuracyPermission : Set where

simulationReceiptDoesNotAutoPromoteToEmpiricalTruth :
  SimulationReceiptImpliesEmpiricalTruthPermission → ⊥
simulationReceiptDoesNotAutoPromoteToEmpiricalTruth ()

reproducibilityDoesNotAutoPromoteToEmpiricalAccuracy :
  ReproducibilityImpliesEmpiricalAccuracyPermission → ⊥
reproducibilityDoesNotAutoPromoteToEmpiricalAccuracy ()

record ConsumerIndexedModelBoundary : Set where
  constructor consumer-indexed-model-boundary
  field
    modelAdequacyIsConsumerIndexed : Bool
    modelAdequacyIsConsumerIndexedIsTrue : modelAdequacyIsConsumerIndexed ≡ true
    simulationOutputIsEmpiricalTruth : Bool
    simulationOutputIsEmpiricalTruthIsFalse : simulationOutputIsEmpiricalTruth ≡ false
    oneConsumerValidationTransfersUniversally : Bool
    oneConsumerValidationTransfersUniversallyIsFalse :
      oneConsumerValidationTransfersUniversally ≡ false

canonicalConsumerIndexedModelBoundary : ConsumerIndexedModelBoundary
canonicalConsumerIndexedModelBoundary =
  consumer-indexed-model-boundary true refl false refl false refl
