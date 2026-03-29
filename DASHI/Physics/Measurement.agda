module DASHI.Physics.Measurement where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
open import DASHI.Physics.QuantumHistory as QH

record PredictionTheory {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ) : Set (lsuc ℓ) where
  field
    Observable : Set ℓ
    Prediction : Observable → Set ℓ

    predict : (O : Observable) → SQ.PhysState Q → Prediction O

record MeasurementTheory {ℓ : Level}
  (Q : SQ.QuotientedTheory ℓ)
  (O : Obs.ObservableTheory Q)
  (K : QH.AmplitudeCarrier ℓ) : Set (lsuc ℓ) where
  field
    Outcome : Obs.ObservableTheory.Observable O → Set ℓ
    Stat    : Set ℓ

    measure :
      (A : Obs.ObservableTheory.Observable O) →
      SQ.PhysState Q →
      Stat

record QuantumMeasurement {ℓ : Level}
  (QS : Set ℓ)
  (K : QH.AmplitudeCarrier ℓ) : Set (lsuc ℓ) where
  field
    ObservableQ : Set ℓ
    OutcomeQ    : ObservableQ → Set ℓ
    PredictionQ : ObservableQ → Set ℓ

    measureQ : (O : ObservableQ) → QS → PredictionQ O

record BornLike {ℓ : Level}
  (K : QH.AmplitudeCarrier ℓ) : Set (lsuc ℓ) where
  open QH.AmplitudeCarrier K
  field
    Weight : Set ℓ
    weight : Amp → Weight
