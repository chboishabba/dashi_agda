module DASHI.Physics.Chemistry.Nobel2026QuantitativeProducerBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- QUANTITATIVE ENANTIOMERIC-EXCESS / KINETIC PRODUCER INTERFACE
--
-- The finite Nobel fixture proves amplification and symmetry structure but does
-- not own a continuous ee curve, reaction-rate law, aggregation mechanism, or
-- calibrated Soai experiment.  This owner makes those remaining obligations
-- typed instead of leaving them as prose.
------------------------------------------------------------------------

record EnantiomericExcessResponseModel : Set₁ where
  constructor enantiomericExcessResponseModel
  field
    EE : Set
    zeroEE : EE
    mirrorEE : EE → EE
    response : EE → EE

    NonZero : EE → Set
    StrongerMagnitude : EE → EE → Set
    SameHandedBranch : EE → EE → Set

    mirrorInvolutive : (e : EE) → mirrorEE (mirrorEE e) ≡ e
    responseMirrorEquivariant :
      (e : EE) → response (mirrorEE e) ≡ mirrorEE (response e)
    zeroResponseFixed : response zeroEE ≡ zeroEE

    positiveNonlinearAmplification :
      (e : EE) → NonZero e → StrongerMagnitude e (response e)
    branchPreservedByResponse :
      (e : EE) → NonZero e → SameHandedBranch e (response e)

open EnantiomericExcessResponseModel public

record SoaiQuantitativeProducer
  (M : EnantiomericExcessResponseModel) : Set₁ where
  constructor soaiQuantitativeProducer
  field
    State : Set
    Time : Set
    Concentration : Set
    RateParameter : Set

    initialState : State
    initialStateTime : Time
    stateAt : Time → State
    eeAt : State → EE M
    productConcentrationAt : Time → Concentration

    productCatalysisEvidence : State → Set
    kineticLawEvidence : Set
    aggregationStateEvidence : Set
    temperatureSolventProtocolEvidence : Set
    measurementCalibrationEvidence : Set
    replicateUncertaintyEvidence : Set

    initialEEIdentity : eeAt initialState ≡ eeAt (stateAt initialStateTime)

    sourceReference : String
    sourceManifestReference : String
    kineticModelReference : String
    aggregationModelReference : String
    measurementProtocolReference : String

open SoaiQuantitativeProducer public

------------------------------------------------------------------------
-- Same-object source payment is intentionally separate from merely supplying
-- any mathematical model with the right qualitative behaviour.
------------------------------------------------------------------------

record QuantitativeSameObjectReceipt
  {M : EnantiomericExcessResponseModel}
  (P : SoaiQuantitativeProducer M) : Set₁ where
  constructor quantitativeSameObjectReceipt
  field
    sourceExperimentIdentity : Set
    sourceInitialEEIdentity : Set
    sourceProductIdentity : Set
    sourceConcentrationIdentity : Set
    sourceTimeAxisIdentity : Set
    sourceTemperatureSolventIdentity : Set
    sourceKineticParameterIdentity : Set
    sourceAggregationIdentity : Set
    modelToMeasuredObservableIdentity : Set

record Nobel2026QuantitativeProducerBoundary : Set where
  constructor nobel2026QuantitativeProducerBoundary
  field
    abstractEEProducerInterfaceOwned : Bool
    abstractKineticProducerInterfaceOwned : Bool
    mirrorEquivarianceRequiredAtQuantitativeLayer : Bool
    sourceSpecificContinuousEEModelInhabitedHere : Bool
    sourceSpecificSoaiKineticProducerInhabitedHere : Bool
    sourceSpecificAggregationMechanismInhabitedHere : Bool
    rawMeasurementCalibrationIngestedHere : Bool
    sameObjectQuantitativeReceiptPaidHere : Bool

canonicalNobel2026QuantitativeProducerBoundary :
  Nobel2026QuantitativeProducerBoundary
canonicalNobel2026QuantitativeProducerBoundary =
  nobel2026QuantitativeProducerBoundary
    true true true false false false false false
