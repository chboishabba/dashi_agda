module DASHI.Physics.Closure.QuantumClockMetricResponseDiscriminatorCompilerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BothwellYe2022RedshiftComparisonExact as Reference
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift

------------------------------------------------------------------------
-- CLOCK METRIC-RESPONSE DISCRIMINATOR BOUNDARY
--
-- A candidate gravity/field model may predict a same-object potential or
-- metric response. The existing redshift law then supplies a declared clock
-- observable. Comparison against an ordinary-gravity reference is useful only
-- for that declared consumer and does not identify the underlying mechanism.
------------------------------------------------------------------------

record MetricClockDiscriminatorBoundary : Set where
  field
    ordinaryGravityComparison : Reference.BothwellYe2022ComparisonReceipt
    ordinaryGravityComparisonIsCanonical :
      ordinaryGravityComparison ≡ Reference.canonicalBothwellYe2022ComparisonReceipt

    redshiftLaw : Redshift.QuantumClockProperTimeRedshiftBridge
    redshiftLawIsCanonical :
      redshiftLaw ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge

    ordinaryGravityReferenceAvailable : Bool
    ordinaryGravityReferenceAvailableIsTrue : ordinaryGravityReferenceAvailable ≡ true

    clockResidualCanBeDeclaredConsumer : Bool
    clockResidualCanBeDeclaredConsumerIsTrue : clockResidualCanBeDeclaredConsumer ≡ true

    candidatePredictionNeedsSameObjectIntervention : Bool
    candidatePredictionNeedsSameObjectInterventionIsTrue :
      candidatePredictionNeedsSameObjectIntervention ≡ true

    sameObjectExperimentalPerturbationPresent : Bool
    sameObjectExperimentalPerturbationPresentIsFalse :
      sameObjectExperimentalPerturbationPresent ≡ false

    candidateMetricResponseObserved : Bool
    candidateMetricResponseObservedIsFalse : candidateMetricResponseObserved ≡ false

    candidateModelValidated : Bool
    candidateModelValidatedIsFalse : candidateModelValidated ≡ false

    referenceCalibrationDoesNotPromoteMechanism : Bool
    referenceCalibrationDoesNotPromoteMechanismIsTrue :
      referenceCalibrationDoesNotPromoteMechanism ≡ true

    reading : List String

open MetricClockDiscriminatorBoundary public

canonicalMetricClockDiscriminatorBoundary : MetricClockDiscriminatorBoundary
canonicalMetricClockDiscriminatorBoundary = record
  { ordinaryGravityComparison = Reference.canonicalBothwellYe2022ComparisonReceipt
  ; ordinaryGravityComparisonIsCanonical = refl
  ; redshiftLaw = Redshift.canonicalQuantumClockProperTimeRedshiftBridge
  ; redshiftLawIsCanonical = refl
  ; ordinaryGravityReferenceAvailable = true
  ; ordinaryGravityReferenceAvailableIsTrue = refl
  ; clockResidualCanBeDeclaredConsumer = true
  ; clockResidualCanBeDeclaredConsumerIsTrue = refl
  ; candidatePredictionNeedsSameObjectIntervention = true
  ; candidatePredictionNeedsSameObjectInterventionIsTrue = refl
  ; sameObjectExperimentalPerturbationPresent = false
  ; sameObjectExperimentalPerturbationPresentIsFalse = refl
  ; candidateMetricResponseObserved = false
  ; candidateMetricResponseObservedIsFalse = refl
  ; candidateModelValidated = false
  ; candidateModelValidatedIsFalse = refl
  ; referenceCalibrationDoesNotPromoteMechanism = true
  ; referenceCalibrationDoesNotPromoteMechanismIsTrue = refl
  ; reading =
      "A candidate model can lawfully hand off to clock metrology only through a declared observable: model-specific potential/metric prediction -> predicted fractional clock shift -> measured residual."
      ∷ "The Bothwell/Ye comparison supplies an ordinary-gravity reference coordinate, not evidence for a different mechanism."
      ∷ "A model-specific claim still needs a controlled same-object experimental perturbation, calibrated readout and candidate-specific adequacy evidence."
      ∷ "Shared algebra or a shared clock carrier therefore cannot promote mechanism identity."
      ∷ []
  }
