module DASHI.Core.FiniteObservationClosureBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Shared theorem-shape only.  This does not equate kinetic truncation,
-- spectroscopy, astronomical filtering, biological screening, or sensor fusion.

data ClosureStage : Set where
  latentState finiteObservation inferredState decisionOrEvolution : ClosureStage

record ObservationClosure : Set₁ where
  constructor observation-closure
  field
    Latent Observation Inference Decision : Set
    observe : Latent → Observation
    infer : Observation → Inference
    decide : Inference → Decision
    reference : String

open ObservationClosure public

record ObservationClosureBoundary : Set where
  constructor observation-closure-boundary
  field
    finiteObservationIsFullLatentState : Bool
    finiteObservationIsFullLatentStateIsFalse : finiteObservationIsFullLatentState ≡ false
    sameObservationImpliesSameLatentState : Bool
    sameObservationImpliesSameLatentStateIsFalse : sameObservationImpliesSameLatentState ≡ false
    inferredStateIsDirectMeasurement : Bool
    inferredStateIsDirectMeasurementIsFalse : inferredStateIsDirectMeasurement ≡ false
    closureNeedsDomainSpecificProducer : Bool
    closureNeedsDomainSpecificProducerIsTrue : closureNeedsDomainSpecificProducer ≡ true

canonicalObservationClosureBoundary : ObservationClosureBoundary
canonicalObservationClosureBoundary = observation-closure-boundary false refl false refl false refl true refl

record ReverseClosureObligation : Set where
  constructor reverse-closure-obligation
  field
    domain : String
    observedCoordinate : String
    missingProducer : String
    whatItWouldPromote : String
    whatItCannotPromote : String

open ReverseClosureObligation public
