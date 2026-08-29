module DASHI.Programmes.QuantumExecutablePromotionReceiptExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- dashiQ executable promotion boundary.
--
-- computer_v2.py already has carrier-dispatched measurement records,
-- promotion strategies, PromotionResult and witness strategies.  The missing
-- formal seam is criterion authority: runtime acceptance is evidence relative
-- to a declared experiment, not physical-theory promotion by itself.
------------------------------------------------------------------------

data QuantumCarrierKind : Set where
  qubit : QuantumCarrierKind
  qutrit : QuantumCarrierKind
  triality : QuantumCarrierKind

record QuantumRuntimeReceipt : Set₁ where
  constructor quantum-runtime-receipt
  field
    State Measurement Criterion Witness : Set

    carrier : QuantumCarrierKind
    measurement : Measurement
    witness : Witness
    accepted : Bool

    criterion : Criterion
    criterionDeclaredBeforeMeasurement : Set
    measurementProducedByCarrierStrategy : Set
    witnessBindsMeasurementAndCriterion : Set

open QuantumRuntimeReceipt public

record QuantumExecutablePromotionBoundary : Set where
  constructor quantum-executable-promotion-boundary
  field
    runtimeAcceptedMeansEstablishedPhysicalTheory : Bool
    runtimeAcceptedMeansEstablishedPhysicalTheoryIsFalse :
      runtimeAcceptedMeansEstablishedPhysicalTheory ≡ false

    carrierNativeSelectionScoreIsFalsifiableObservableByDefault : Bool
    carrierNativeSelectionScoreIsFalsifiableObservableByDefaultIsFalse :
      carrierNativeSelectionScoreIsFalsifiableObservableByDefault ≡ false

    postHocPromotionThresholdIsIndependentExperimentCriterion : Bool
    postHocPromotionThresholdIsIndependentExperimentCriterionIsFalse :
      postHocPromotionThresholdIsIndependentExperimentCriterion ≡ false

    predeclaredCriterionPlusBoundWitnessCanSupportExperimentReceipt : Bool
    predeclaredCriterionPlusBoundWitnessCanSupportExperimentReceiptIsTrue :
      predeclaredCriterionPlusBoundWitnessCanSupportExperimentReceipt ≡ true

    experimentReceiptStillNeedsPhysicalPromotionGate : Bool
    experimentReceiptStillNeedsPhysicalPromotionGateIsTrue :
      experimentReceiptStillNeedsPhysicalPromotionGate ≡ true

canonicalQuantumExecutablePromotionBoundary : QuantumExecutablePromotionBoundary
canonicalQuantumExecutablePromotionBoundary =
  quantum-executable-promotion-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
