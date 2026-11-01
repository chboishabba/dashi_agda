module DASHI.Physics.Closure.EmpiricalCosmologyValidationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Empirical cosmology validation boundary.
--
-- Formal consistency is not empirical cosmology.  A cosmological model becomes
-- empirical only after observables, calibration, uncertainty, null models,
-- preregistered tests, and external data are connected to the theory.

record CosmologyPrediction : Set where
  constructor mkCosmologyPrediction
  field
    predictionLabel : String
    parameterCount : Nat
    observableCount : Nat
    quantitativeValuesLockedBeforeEvaluation : Bool
    predictionScope : String

open CosmologyPrediction public

record CosmologyDataset : Set where
  constructor mkCosmologyDataset
  field
    datasetLabel : String
    independentOfModelConstruction : Bool
    calibrationDocumented : Bool
    covarianceSupplied : Bool
    selectionEffectsModelled : Bool
    datasetScope : String

open CosmologyDataset public

record EmpiricalTest
  (prediction : CosmologyPrediction)
  (dataset : CosmologyDataset) : Set where
  constructor mkEmpiricalTest
  field
    likelihoodOrLossSpecified : Bool
    nullModelSpecified : Bool
    preregisteredDecisionRule : Bool
    parameterPenaltyIncluded : Bool
    posteriorPredictiveOrHoldoutCheck : Bool
    systematicSensitivityChecked : Bool
    resultReproducible : Bool
    modelPassesLockedCriterion : Bool
    testScope : String

open EmpiricalTest public

record EmpiricalCosmologyReceipt : Set where
  constructor mkEmpiricalCosmologyReceipt
  field
    prediction : CosmologyPrediction
    dataset : CosmologyDataset
    test : EmpiricalTest prediction dataset
    externalReplicationAvailable : Bool
    validatedNovelPrediction : Bool
    receiptScope : String

open EmpiricalCosmologyReceipt public

record EmpiricalCosmologyPromotionBoundary : Set where
  constructor mkEmpiricalCosmologyPromotionBoundary
  field
    validationProtocolImplemented : Bool
    repositoryContainsLockedPhysicalPrediction : Bool
    repositoryContainsIndependentCosmologyDataset : Bool
    empiricalFitCompleted : Bool
    externalReplicationCompleted : Bool
    empiricalCosmologyClaimPermitted : Bool
    boundaryStatement : String

open EmpiricalCosmologyPromotionBoundary public

canonicalEmpiricalCosmologyPromotionBoundary : EmpiricalCosmologyPromotionBoundary
canonicalEmpiricalCosmologyPromotionBoundary =
  mkEmpiricalCosmologyPromotionBoundary
    true false false false false false
    "a falsifiable empirical protocol is typed; no dataset fit, replication, or empirical cosmology result is present"

canonicalEmpiricalCosmologyBlocked :
  empiricalCosmologyClaimPermitted canonicalEmpiricalCosmologyPromotionBoundary ≡ false
canonicalEmpiricalCosmologyBlocked = refl

emptyPrediction : CosmologyPrediction
emptyPrediction =
  mkCosmologyPrediction
    "no-locked-prediction"
    zero zero false
    "placeholder proving the protocol type is inhabited, not an empirical prediction"
