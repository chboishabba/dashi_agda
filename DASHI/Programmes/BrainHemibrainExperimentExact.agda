module DASHI.Programmes.BrainHemibrainExperimentExact where

open import DASHI.Core.Prelude
open import DASHI.Core.PredictionEnvelopeExact

------------------------------------------------------------------------
-- dashiBRAIN literal experiment socket.
--
-- The satellite computes ternarised connectome states, kernel/defect structure,
-- and later coarse-graining measurements.  This module does not assert any
-- empirical hemibrain result.  It states the exact evidence/measurement seam
-- required before such a result can close a downstream prediction envelope.
------------------------------------------------------------------------

record HemibrainExperimentInterface : Set₁ where
  constructor hemibrainExperimentInterface
  field
    State Evidence Measurement Prediction : Set
    compatible : Compatible Evidence State
    measure : State → Measurement
    consumer : State → Prediction
    KernelClosed : State → Set
    LowDefect : State → Set
    CoarsePersistent : State → Set

open HemibrainExperimentInterface public

HemibrainMeasuredCompatible :
  (h : HemibrainExperimentInterface) →
  Evidence h × Measurement h → State h → Set
HemibrainMeasuredCompatible h =
  MeasuredCompatible (compatible h) (measure h)

HemibrainMeasurementClosesPrediction :
  (h : HemibrainExperimentInterface) →
  Evidence h × Measurement h → Set
HemibrainMeasurementClosesPrediction h =
  MeasurementClosesEnvelope
    (compatible h)
    (measure h)
    (consumer h)

------------------------------------------------------------------------
-- Persistent low-defect kernel closure is a hypothesis on the same state,
-- not evidence of prediction-identifiability by itself.  A closing measurement
-- must still discharge the consumer-relative envelope condition above.
------------------------------------------------------------------------

record HemibrainCandidateReceipt
    (h : HemibrainExperimentInterface)
    (state : State h) : Set where
  constructor hemibrainCandidateReceipt
  field
    kernelClosedReceipt : KernelClosed h state
    lowDefectReceipt : LowDefect h state
    coarsePersistenceReceipt : CoarsePersistent h state

hemibrainReceiptDoesNotRemoveMeasurementObligation :
  ∀ (h : HemibrainExperimentInterface)
    (state : State h) →
  HemibrainCandidateReceipt h state →
  (evidence : Evidence h × Measurement h) →
  HemibrainMeasurementClosesPrediction h evidence →
  HemibrainMeasurementClosesPrediction h evidence
hemibrainReceiptDoesNotRemoveMeasurementObligation h state receipt evidence closes = closes
