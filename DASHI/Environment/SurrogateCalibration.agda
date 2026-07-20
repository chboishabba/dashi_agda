module DASHI.Environment.SurrogateCalibration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_≤_)

import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Environment.QuantitiesConservation as Q

record ModelIdentity : Set where
  constructor mkModelIdentity
  field
    modelName : String
    modelVersion : String
    sourceRevision : String
    configurationHash : String
    authorityClass : String
open ModelIdentity public

record InputDomain : Set where
  constructor mkInputDomain
  field
    domainName : String
    variableNames : List String
    unitDeclarations : List String
    spatialExtent : String
    temporalExtent : String
    parameterBounds : List String
    exclusions : List String
open InputDomain public

record TrainingCoverage : Set where
  constructor mkTrainingCoverage
  field
    scenarioCount : Nat
    climateRegimes : List String
    soilRegimes : List String
    managementRegimes : List String
    interventionRegimes : List String
    heldOutScenarioCount : Nat
    coverageReference : String
open TrainingCoverage public

record OutputContract : Set where
  constructor mkOutputContract
  field
    outputNames : List String
    outputUnits : List String
    aggregationRules : List String
    missingValuePolicy : String
open OutputContract public

record LatentModelContract : Set₁ where
  constructor mkLatentModelContract
  field
    Input : Set
    Output : Set
    Latent : Set
    encode : Input → Latent
    predict : Latent → Output
    uncertainty : Latent → Nat
    insideDeclaredSupport : Input → Bool
open LatentModelContract public

record HeldOutValidation : Set where
  constructor mkHeldOutValidation
  field
    validationDataset : String
    sampleCount : Nat
    errorBound : Nat
    observedMaximumError : Nat
    observedErrorWithinBound : observedMaximumError ≤ errorBound
    calibrationMethod : String
    calibrationReference : String
open HeldOutValidation public

record CalibrationReceipt : Set₁ where
  constructor mkCalibrationReceipt
  field
    authoritativeModel : ModelIdentity
    inputDomain : InputDomain
    coverage : TrainingCoverage
    outputs : OutputContract
    latentContract : LatentModelContract
    heldOut : HeldOutValidation
    conservation : Q.ConservationBundle
    uncertaintyThreshold : Nat
    residualThreshold : Nat
    escalationPolicy : String
    provenance : List String
open CalibrationReceipt public

record SurrogateAssessment : Set where
  constructor mkSurrogateAssessment
  field
    insideSupport : Bool
    measuredResidual : Nat
    residualThreshold : Nat
    residualAcceptable : measuredResidual ≤ residualThreshold
    measuredUncertainty : Nat
    uncertaintyThreshold : Nat
    uncertaintyAcceptable : measuredUncertainty ≤ uncertaintyThreshold
    conservationPassed : Bool
    policyCritical : Bool
open SurrogateAssessment public

assessmentEscalation : SurrogateAssessment → Latent.EscalationEvidence
assessmentEscalation a =
  Latent.mkEscalationEvidence
    (not (insideSupport a))
    (not (leqBool (measuredResidual a) (residualThreshold a)))
    (not (leqBool (measuredUncertainty a) (uncertaintyThreshold a)))
    (not (conservationPassed a))
    (policyCritical a)
  where
    not : Bool → Bool
    not true = false
    not false = true

    leqBool : Nat → Nat → Bool
    leqBool zero y = true
    leqBool (suc x) zero = false
    leqBool (suc x) (suc y) = leqBool x y

record SurrogateUseReceipt : Set where
  constructor mkSurrogateUseReceipt
  field
    startingLane : Latent.ModelLane
    assessment : SurrogateAssessment
    resultingLane : Latent.ModelLane
    laneMatches :
      resultingLane ≡
      Latent.chooseLane startingLane (assessmentEscalation assessment)
    modelReference : String
    humanReviewRequired : Bool
open SurrogateUseReceipt public

record SurrogateBoundary : Set where
  constructor mkSurrogateBoundary
  field
    calibrationIsEmpiricalNotUniversalProof : Bool
    heldOutValidationRequired : Bool
    supportExtrapolationEscalates : Bool
    uncertaintyEscalates : Bool
    conservationFailureEscalates : Bool
    policyCriticalUseEscalates : Bool
open SurrogateBoundary public

canonicalSurrogateBoundary : SurrogateBoundary
canonicalSurrogateBoundary =
  mkSurrogateBoundary true true true true true true
