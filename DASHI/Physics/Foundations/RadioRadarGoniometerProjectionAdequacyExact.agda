module DASHI.Physics.Foundations.RadioRadarGoniometerProjectionAdequacyExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as DF

------------------------------------------------------------------------
-- Query-indexed projection adequacy, specialised to the finite DF witness.
-- The observation projection is bearing only.  A consumer that asks for the
-- exact emitter world cannot factor through that projection because two
-- distinct worlds share the same observed bearing.

ExactEmitterWorldConsumer : Set
ExactEmitterWorldConsumer = DF.EmitterWorld → DF.EmitterWorld

exactEmitterWorldQuery : ExactEmitterWorldConsumer
exactEmitterWorldQuery x = x

BearingFactorisation : Set
BearingFactorisation =
  Σ (DF.BearingObservation → DF.EmitterWorld) λ recover →
    (x : DF.EmitterWorld) →
    recover (DF.observeBearing x) ≡ exactEmitterWorldQuery x

bearingProjectionCannotServeExactWorldConsumer : ¬ BearingFactorisation
bearingProjectionCannotServeExactWorldConsumer (recover , factors) =
  DF.nearAndFarWorldsDistinct
    (trans
      (sym (factors DF.nearEmitterNorthEast))
      (factors DF.farEmitterNorthEast))

------------------------------------------------------------------------
-- A bearing-valued consumer does factor through the same projection.  This
-- records the query-relative character of adequacy rather than declaring the
-- observation globally good or bad.

BearingConsumer : Set
BearingConsumer = DF.EmitterWorld → DF.BearingObservation

bearingQuery : BearingConsumer
bearingQuery = DF.observeBearing

BearingQueryFactorisation : Set
BearingQueryFactorisation =
  Σ (DF.BearingObservation → DF.BearingObservation) λ recover →
    (x : DF.EmitterWorld) →
    recover (DF.observeBearing x) ≡ bearingQuery x

bearingProjectionServesBearingConsumer : BearingQueryFactorisation
bearingProjectionServesBearingConsumer =
  ((λ x → x) , λ _ → refl)
