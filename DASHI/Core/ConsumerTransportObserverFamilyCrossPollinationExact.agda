module DASHI.Core.ConsumerTransportObserverFamilyCrossPollinationExact where

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

addingConsumerShrinksResidual :
  ∀ {State Action Consumer Observation : Set}
    (family : Plural.ConsumerProjectionFamily State Action Consumer Observation)
    (consumer : Consumer) (rest : List Consumer) (state : State) →
  Observer.ResidualObservationFibre
    (selectedConsumerObservers family (consumer ∷ rest)) state →
  Observer.ResidualObservationFibre
    (selectedConsumerObservers family rest) state
addingConsumerShrinksResidual family =
  Indexed.addingIndexShrinksResidualFibre (Plural.project family)

addingTransportObserverShrinksResidual :
  (system : Transport.TransportSystem)
  (observer : Transport.Observer system)
  (rest : List (Transport.Observer system))
  (state : Transport.State system) →
  Observer.ResidualObservationFibre
    (selectedTransportObservers system (observer ∷ rest)) state →
  Observer.ResidualObservationFibre
    (selectedTransportObservers system rest) state
addingTransportObserverShrinksResidual system =
  Indexed.addingIndexShrinksResidualFibre (Transport.observe system)

-- Structural reuse only: consumer != physical sensor, and static refinement
-- grants neither plural dynamic safety nor physical fidelity.
