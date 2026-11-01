module DASHI.Core.ConsumerTransportObserverFamilyCrossPollinationExact where

------------------------------------------------------------------------
-- CONSUMER PROJECTIONS AND PHYSICAL OBSERVERS SHARE ONE STATIC INDEX SHAPE
--
-- This is a structural cross-pollination only.  A policy consumer and a camera
-- pixel/microphone are not identified semantically.  Both existing modules do,
-- however, export an index -> State -> Observation function, so both can reuse
-- the same finite observer-family/refinement machinery.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IndexedObserverFamilyBridgeExact as Indexed
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Physics.ObserverConditionedTransportBridge as Transport

selectedConsumerObservers :
  ∀ {State Action Consumer Observation : Set}
    (family : Plural.ConsumerProjectionFamily State Action Consumer Observation) →
  List Consumer → Observer.ObserverFamily State Observation
selectedConsumerObservers family =
  Indexed.selectedObserverFamily (Plural.project family)

selectedTransportObservers :
  (system : Transport.TransportSystem) →
  List (Transport.Observer system) →
  Observer.ObserverFamily (Transport.State system) (Transport.Sample system)
selectedTransportObservers system =
  Indexed.selectedObserverFamily (Transport.observe system)

addingConsumerShrinksStaticResidualFibre :
  ∀ {State Action Consumer Observation : Set}
    (family : Plural.ConsumerProjectionFamily State Action Consumer Observation)
    (consumer : Consumer)
    (rest : List Consumer)
    (state : State) →
  Observer.ResidualObservationFibre
    (selectedConsumerObservers family (consumer ∷ rest)) state →
  Observer.ResidualObservationFibre
    (selectedConsumerObservers family rest) state
addingConsumerShrinksStaticResidualFibre family =
  Indexed.addingIndexShrinksResidualFibre (Plural.project family)

addingTransportObserverShrinksStaticResidualFibre :
  (system : Transport.TransportSystem)
  (observer : Transport.Observer system)
  (rest : List (Transport.Observer system))
  (state : Transport.State system) →
  Observer.ResidualObservationFibre
    (selectedTransportObservers system (observer ∷ rest)) state →
  Observer.ResidualObservationFibre
    (selectedTransportObservers system rest) state
addingTransportObserverShrinksStaticResidualFibre system =
  Indexed.addingIndexShrinksResidualFibre (Transport.observe system)

record ConsumerTransportObserverCrossPollinationBoundary : Set where
  constructor consumerTransportObserverCrossPollinationBoundary
  field
    commonIndexedObserverShapeReused : Bool
    commonIndexedObserverShapeReusedIsTrue :
      commonIndexedObserverShapeReused ≡ true
    addingConsumerShrinksStaticCollisionFibre : Bool
    addingConsumerShrinksStaticCollisionFibreIsTrue :
      addingConsumerShrinksStaticCollisionFibre ≡ true
    addingSensorShrinksStaticCollisionFibre : Bool
    addingSensorShrinksStaticCollisionFibreIsTrue :
      addingSensorShrinksStaticCollisionFibre ≡ true
    policyConsumerEqualsPhysicalSensor : Bool
    policyConsumerEqualsPhysicalSensorIsFalse :
      policyConsumerEqualsPhysicalSensor ≡ false
    staticRefinementAutomaticallyProvesPluralDynamicSafety : Bool
    staticRefinementAutomaticallyProvesPluralDynamicSafetyIsFalse :
      staticRefinementAutomaticallyProvesPluralDynamicSafety ≡ false
    staticRefinementAutomaticallyProvesPhysicalFidelity : Bool
    staticRefinementAutomaticallyProvesPhysicalFidelityIsFalse :
      staticRefinementAutomaticallyProvesPhysicalFidelity ≡ false

canonicalConsumerTransportObserverCrossPollinationBoundary :
  ConsumerTransportObserverCrossPollinationBoundary
canonicalConsumerTransportObserverCrossPollinationBoundary =
  consumerTransportObserverCrossPollinationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
