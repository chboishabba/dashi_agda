module DASHI.Core.ObserverIncomparabilityCrosswalkExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementCore as Core
import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ObserverRefinementOrientationCrosswalkExact as Orientation
import DASHI.Core.ObserverIncomparabilityTypedJoinExact as TypedJoin

------------------------------------------------------------------------
-- INCOMPARABILITY / CROSS-COLLISION CROSSWALK
--
-- `ObserverRefinementCore.CrossCollision` and
-- `ObserverIncomparabilityTypedJoinExact.IncomparableObservers` carry the same
-- two finite collisions with opposite observers doing the separating.  Keep
-- both historical APIs, but make the exact translation explicit so future
-- consumers do not invent a third carrier.
------------------------------------------------------------------------

typedIncomparableToCoreCrossCollision :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Core.CrossCollision left right
typedIncomparableToCoreCrossCollision witness =
  Core.crossCollision
    (TypedJoin.leftCollision₁ witness)
    (TypedJoin.leftCollision₂ witness)
    (TypedJoin.leftSame witness)
    (TypedJoin.rightSplitsLeftCollision witness)
    (TypedJoin.rightCollision₁ witness)
    (TypedJoin.rightCollision₂ witness)
    (TypedJoin.rightSame witness)
    (TypedJoin.leftSplitsRightCollision witness)

coreCrossCollisionToTypedIncomparable :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  Core.CrossCollision left right →
  TypedJoin.IncomparableObservers left right
coreCrossCollisionToTypedIncomparable witness =
  TypedJoin.incomparableObservers
    (Core.a₁ witness)
    (Core.a₂ witness)
    (Core.sameA witness)
    (Core.differentB witness)
    (Core.b₁ witness)
    (Core.b₂ witness)
    (Core.sameB witness)
    (Core.differentA witness)

typedJoinStrictLeftToCore :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Core.StrictlyRefines (Core.pairObserver left right) left
typedJoinStrictLeftToCore witness =
  Core.pairStrictlyRefinesLeft
    (typedIncomparableToCoreCrossCollision witness)

typedJoinStrictRightToCore :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Core.StrictlyRefines (Core.pairObserver left right) right
typedJoinStrictRightToCore witness =
  Core.pairStrictlyRefinesRight
    (typedIncomparableToCoreCrossCollision witness)

typedJoinStrictLeftToLattice :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Lattice.StrictRefinement left (Core.pairObserver left right)
typedJoinStrictLeftToLattice witness =
  Orientation.coreStrictToLattice (typedJoinStrictLeftToCore witness)

typedJoinStrictRightToLattice :
  ∀ {State A B : Set}
    {left : State → A}
    {right : State → B} →
  TypedJoin.IncomparableObservers left right →
  Lattice.StrictRefinement right (Core.pairObserver left right)
typedJoinStrictRightToLattice witness =
  Orientation.coreStrictToLattice (typedJoinStrictRightToCore witness)
