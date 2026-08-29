module DASHI.Programmes.TestHarnessEvidenceCorrectionExact where

open import DASHI.Core.Prelude
open import DASHI.Core.PredictionEnvelopeExact

------------------------------------------------------------------------
-- BIDI cut for dashitest.
--
-- The heterogeneous harness may emit many numerical or visual artifacts.  A
-- theorem-facing result is instead a typed witness that one declared prediction
-- lies in the evidence fibre of one declared consumer.  Uniqueness remains a
-- separate obligation.
------------------------------------------------------------------------

record TypedExperimentReceipt
    (Evidence State Prediction : Set)
    (compatible : Compatible Evidence State)
    (consumer : State → Prediction) : Set₁ where
  constructor typedExperimentReceipt
  field
    evidence : Evidence
    prediction : Prediction
    envelopeWitness :
      PredictionEnvelope compatible consumer evidence prediction

open TypedExperimentReceipt public

receiptProvidesAdmissiblePrediction :
  ∀ {Evidence State Prediction : Set}
    {compatible : Compatible Evidence State}
    {consumer : State → Prediction} →
  (receipt : TypedExperimentReceipt Evidence State Prediction compatible consumer) →
  PredictionEnvelope compatible consumer
    (evidence receipt)
    (prediction receipt)
receiptProvidesAdmissiblePrediction receipt = envelopeWitness receipt

receiptPlusUniquenessPinsPrediction :
  ∀ {Evidence State Prediction : Set}
    {compatible : Compatible Evidence State}
    {consumer : State → Prediction}
    (receipt : TypedExperimentReceipt Evidence State Prediction compatible consumer) →
  EnvelopeUnique compatible consumer (evidence receipt) →
  ∀ {other : Prediction} →
  PredictionEnvelope compatible consumer (evidence receipt) other →
  prediction receipt ≡ other
receiptPlusUniquenessPinsPrediction receipt unique otherWitness =
  unique (envelopeWitness receipt) otherWitness

record TestHarnessEvidenceCorrectionBoundary : Set where
  constructor testHarnessEvidenceCorrectionBoundary
  field
    plotOrMetricIsProofByItself : Bool
    plotOrMetricIsProofByItselfIsFalse :
      plotOrMetricIsProofByItself ≡ false

    oneEnvelopeWitnessGivesUniqueness : Bool
    oneEnvelopeWitnessGivesUniquenessIsFalse :
      oneEnvelopeWitnessGivesUniqueness ≡ false

    typedReceiptPlusUniquenessMayPinPrediction : Bool
    typedReceiptPlusUniquenessMayPinPredictionIsTrue :
      typedReceiptPlusUniquenessMayPinPrediction ≡ true

canonicalTestHarnessEvidenceCorrectionBoundary :
  TestHarnessEvidenceCorrectionBoundary
canonicalTestHarnessEvidenceCorrectionBoundary =
  testHarnessEvidenceCorrectionBoundary
    false refl
    false refl
    true refl
