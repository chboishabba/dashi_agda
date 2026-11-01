module DASHI.Algebra.Quantum.MeasurementPromotionBridgeTests where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat using (z≤n; s≤s)

import DASHI.Algebra.Quantum.MeasurementPromotionBridge as Bridge

------------------------------------------------------------------------
-- Focused executable witness for
--
--   latent state → reversible evolution → measurement record → promotion.
------------------------------------------------------------------------

unitEvolution : Bridge.ReversibleEvolution ⊤
unitEvolution =
  record
    { step = λ state → state
    ; inv = λ state → state
    ; left = λ state → refl
    ; right = λ state → refl
    }

data Datum : Set where
  observed : Datum

unitMeasurement : Bridge.MeasurementOp ⊤ Datum
unitMeasurement =
  record
    { project = λ state → state
    ; project-idempotent = λ state → refl
    ; measure = λ _ → observed
    }

unitRecord : Bridge.MeasurementRecord unitMeasurement
unitRecord = Bridge.runMeasurement unitMeasurement tt

unitPipeline : Bridge.QuantumMeasurementPipeline unitEvolution unitMeasurement
unitPipeline = Bridge.runPipeline unitEvolution unitMeasurement tt

unitPipelineStartsAtInput :
  Bridge.QuantumMeasurementPipeline.stateIn unitPipeline ≡ tt
unitPipelineStartsAtInput = refl

unitPipelineMeasuresEvolvedState :
  Bridge.MeasurementRecord.latentBefore
    (Bridge.QuantumMeasurementPipeline.measurementRecord unitPipeline)
  ≡
  Bridge.QuantumMeasurementPipeline.stateEvolved unitPipeline
unitPipelineMeasuresEvolvedState =
  Bridge.QuantumMeasurementPipeline.recordStartsAtEvolved unitPipeline

unitPolicy : Bridge.PromotionPolicy unitMeasurement
unitPolicy =
  record
    { Candidate = λ _ → ⊤
    ; evidenceLedger = λ _ →
        record
          { nullCodeLength = suc (suc (suc zero))
          ; structuredCodeLength = suc zero
          ; selectionCost = zero
          ; minimumGain = suc zero
          }
    }

unitEvidenceSufficient :
  Bridge.EvidenceSufficient
    (Bridge.PromotionPolicy.evidenceLedger unitPolicy unitRecord)
unitEvidenceSufficient = s≤s (s≤s z≤n)

unitPromoted : Bridge.Promoted unitPolicy unitRecord
unitPromoted =
  Bridge.promote unitPolicy unitRecord tt unitEvidenceSufficient

unitPromotionCarriesCandidate :
  Bridge.PromotionPolicy.Candidate unitPolicy unitRecord
unitPromotionCarriesCandidate =
  Bridge.promotion-fail-closed-candidate unitPolicy unitRecord unitPromoted

unitPromotionCarriesEvidence :
  Bridge.EvidenceSufficient
    (Bridge.PromotionPolicy.evidenceLedger unitPolicy unitRecord)
unitPromotionCarriesEvidence =
  Bridge.promotion-fail-closed-evidence unitPolicy unitRecord unitPromoted
