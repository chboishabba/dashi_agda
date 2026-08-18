module DASHI.Core.IndexedObserverFamilyBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

selectedObserverFamily :
  ∀ {Index State Value : Set} →
  (Index → State → Value) → List Index → Observer.ObserverFamily State Value
selectedObserverFamily observe [] = []
selectedObserverFamily observe (i ∷ is) =
  observe i ∷ selectedObserverFamily observe is

addingIndexRefinesSelectedFamily :
  ∀ {Index State Value : Set}
    (observe : Index → State → Value)
    (i : Index) (is : List Index) →
  Observer.FamilyRefines
    (selectedObserverFamily observe is)
    (selectedObserverFamily observe (i ∷ is))
addingIndexRefinesSelectedFamily observe i is =
  Observer.prependFamilyRefinesTail
    (observe i) (selectedObserverFamily observe is)

addingIndexShrinksResidualFibre :
  ∀ {Index State Value : Set}
    (observe : Index → State → Value)
    (i : Index) (is : List Index) (x : State) →
  Observer.ResidualObservationFibre
    (selectedObserverFamily observe (i ∷ is)) x →
  Observer.ResidualObservationFibre
    (selectedObserverFamily observe is) x
addingIndexShrinksResidualFibre observe i is x =
  Observer.addingObserverShrinksResidualFibre
    (observe i) (selectedObserverFamily observe is) x
