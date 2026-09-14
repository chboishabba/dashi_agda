module DASHI.Core.ObserverIncomparabilityCrosswalkRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ObserverIncomparabilityTypedJoinExact as TypedJoin
import DASHI.Core.ObserverIncomparabilityCrosswalkExact as Crosswalk

roundTripIntoCoreCarrier :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Core.CrossCollision left right
roundTripIntoCoreCarrier = Crosswalk.typedIncomparableToCoreCrossCollision

roundTripIntoTypedCarrier :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  Core.CrossCollision left right →
  TypedJoin.IncomparableObservers left right
roundTripIntoTypedCarrier = Crosswalk.coreCrossCollisionToTypedIncomparable

typedWitnessYieldsCoreStrictLeft :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Core.StrictlyRefines (Core.pairObserver left right) left
typedWitnessYieldsCoreStrictLeft = Crosswalk.typedJoinStrictLeftToCore

typedWitnessYieldsCanonicalLatticeStrictRight :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Lattice.StrictRefinement right (Core.pairObserver left right)
typedWitnessYieldsCanonicalLatticeStrictRight =
  Crosswalk.typedJoinStrictRightToLattice
