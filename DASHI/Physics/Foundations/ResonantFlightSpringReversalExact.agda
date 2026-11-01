module DASHI.Physics.Foundations.ResonantFlightSpringReversalExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Stroke reversal is represented as exchange between wing kinetic state
-- and elastic state, optionally mediated by a bus.
------------------------------------------------------------------------

record ReversalExchange : Set₁ where
  constructor reversal-exchange
  field
    WingKinetic ElasticState : Set
    wingToElastic : WingKinetic → ElasticState
    elasticToWing : ElasticState → WingKinetic

open ReversalExchange public

record BusMediatedReversal : Set₁ where
  constructor bus-mediated-reversal
  field
    WingKinetic ElasticState BusState : Set
    wingToElastic : WingKinetic → ElasticState
    elasticToBus : ElasticState → BusState
    busToElastic : BusState → ElasticState
    elasticToWing : ElasticState → WingKinetic

open BusMediatedReversal public

roundTripReversal :
  (R : BusMediatedReversal) →
  WingKinetic R →
  WingKinetic R
roundTripReversal R w =
  elasticToWing R
    (busToElastic R
      (elasticToBus R
        (wingToElastic R w)))
