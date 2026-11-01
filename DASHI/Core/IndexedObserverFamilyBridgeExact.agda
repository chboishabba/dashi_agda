module DASHI.Core.IndexedObserverFamilyBridgeExact where

------------------------------------------------------------------------
-- INDEXED OBSERVERS -> STATIC OBSERVER FAMILY
--
-- A number of repo domains already have the same raw shape:
--
--   index -> State -> Value
--
-- where the index may be a consumer, sensor, microphone, pixel, query, or
-- other declared observation context.  This adapter only packages a finite
-- selected index list into ObserverRefinementLatticeExact.  It does NOT grant
-- dynamic safety, world completeness, identity authority, or physical
-- sufficiency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

selectedObserverFamily :
  ∀ {Index State Value : Set} →
  (observe : Index → State → Value) →
  List Index →
  Observer.ObserverFamily State Value
selectedObserverFamily observe [] = []
selectedObserverFamily observe (index ∷ rest) =
  observe index ∷ selectedObserverFamily observe rest

addingIndexRefinesSelectedFamily :
  ∀ {Index State Value : Set}
    (observe : Index → State → Value)
    (index : Index)
    (rest : List Index) →
  Observer.FamilyRefines
    (selectedObserverFamily observe rest)
    (selectedObserverFamily observe (index ∷ rest))
addingIndexRefinesSelectedFamily observe index rest =
  Observer.prependFamilyRefinesTail
    (observe index)
    (selectedObserverFamily observe rest)

addingIndexShrinksResidualFibre :
  ∀ {Index State Value : Set}
    (observe : Index → State → Value)
    (index : Index)
    (rest : List Index)
    (state : State) →
  Observer.ResidualObservationFibre
    (selectedObserverFamily observe (index ∷ rest)) state →
  Observer.ResidualObservationFibre
    (selectedObserverFamily observe rest) state
addingIndexShrinksResidualFibre observe index rest state =
  Observer.addingObserverShrinksResidualFibre
    (observe index)
    (selectedObserverFamily observe rest)
    state

record IndexedObserverFamilyBoundary : Set where
  constructor indexedObserverFamilyBoundary
  field
    finiteIndexListsGiveObserverFamilies : Bool
    finiteIndexListsGiveObserverFamiliesIsTrue :
      finiteIndexListsGiveObserverFamilies ≡ true
    addingIndexMonotonicallyShrinksResidualFibre : Bool
    addingIndexMonotonicallyShrinksResidualFibreIsTrue :
      addingIndexMonotonicallyShrinksResidualFibre ≡ true
    selectedFamilyAutomaticallyDynamicallySafe : Bool
    selectedFamilyAutomaticallyDynamicallySafeIsFalse :
      selectedFamilyAutomaticallyDynamicallySafe ≡ false
    selectedFamilyAutomaticallyWorldComplete : Bool
    selectedFamilyAutomaticallyWorldCompleteIsFalse :
      selectedFamilyAutomaticallyWorldComplete ≡ false

canonicalIndexedObserverFamilyBoundary : IndexedObserverFamilyBoundary
canonicalIndexedObserverFamilyBoundary =
  indexedObserverFamilyBoundary
    true refl
    true refl
    false refl
    false refl
