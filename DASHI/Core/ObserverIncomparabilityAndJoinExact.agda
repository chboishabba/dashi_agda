module DASHI.Core.ObserverIncomparabilityAndJoinExact where

------------------------------------------------------------------------
-- OBSERVER INCOMPARABILITY AND LEAST JOINT REFINEMENT
--
-- This is the generic theorem extracted from the transverse-collision pattern
-- now appearing independently in Base369 aggregation/orientation, marked Hecke
-- representation observers, multi-outcome policy surfaces, and other DASHI
-- consumers.
--
-- Refines coarse fine means: equality under the fine observer implies equality
-- under the coarse observer.  Hence "fine" carries at least the distinctions
-- required by "coarse".  Two observers are incomparable when each has a fibre
-- collision split by the other.  Their paired observer is then a strict
-- refinement of each, and is the least common refinement in this information
-- preorder.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer

record CrossCollision
    {State A B : Set}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) : Set where
  constructor crossCollision
  field
    leftCollisionX leftCollisionY : State
    leftSame : left leftCollisionX ≡ left leftCollisionY
    rightSplitsLeftCollision :
      right leftCollisionX ≡ right leftCollisionY → ⊥

    rightCollisionX rightCollisionY : State
    rightSame : right rightCollisionX ≡ right rightCollisionY
    leftSplitsRightCollision :
      left rightCollisionX ≡ left rightCollisionY → ⊥

open CrossCollision public

-- If left equality can occur while right differs, then left cannot be a fine
-- refinement of right: Refines right left would force right equality.
leftCannotRefineRight :
  ∀ {State A B}
    {left : Observer.Observer State A}
    {right : Observer.Observer State B} →
  CrossCollision left right →
  Observer.Refines right left →
  ⊥
leftCannotRefineRight witness refinement =
  rightSplitsLeftCollision witness
    (refinement
      (leftCollisionX witness)
      (leftCollisionY witness)
      (leftSame witness))

-- Symmetrically, right cannot be a fine refinement of left.
rightCannotRefineLeft :
  ∀ {State A B}
    {left : Observer.Observer State A}
    {right : Observer.Observer State B} →
  CrossCollision left right →
  Observer.Refines left right →
  ⊥
rightCannotRefineLeft witness refinement =
  leftSplitsRightCollision witness
    (refinement
      (rightCollisionX witness)
      (rightCollisionY witness)
      (rightSame witness))

record Incomparable
    {State A B : Set}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) : Set where
  constructor incomparable
  field
    leftNotFineEnoughForRight : Observer.Refines right left → ⊥
    rightNotFineEnoughForLeft : Observer.Refines left right → ⊥

open Incomparable public

crossCollisionImpliesIncomparable :
  ∀ {State A B}
    {left : Observer.Observer State A}
    {right : Observer.Observer State B} →
  CrossCollision left right →
  Incomparable left right
crossCollisionImpliesIncomparable witness =
  incomparable
    (leftCannotRefineRight witness)
    (rightCannotRefineLeft witness)

jointObserver :
  ∀ {State A B} →
  Observer.Observer State A →
  Observer.Observer State B →
  Observer.Observer State (A × B)
jointObserver = Observer.pairObserver

jointRefinesLeft :
  ∀ {State A B}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) →
  Observer.Refines left (jointObserver left right)
jointRefinesLeft = Observer.pairRefinesLeft

jointRefinesRight :
  ∀ {State A B}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) →
  Observer.Refines right (jointObserver left right)
jointRefinesRight = Observer.pairRefinesRight

crossCollisionMakesJointStrictOverLeft :
  ∀ {State A B}
    {left : Observer.Observer State A}
    {right : Observer.Observer State B} →
  CrossCollision left right →
  Observer.StrictRefinement left (jointObserver left right)
crossCollisionMakesJointStrictOverLeft {left = left} {right = right} witness =
  Observer.strictRefinement
    (jointRefinesLeft left right)
    (leftCollisionX witness)
    (leftCollisionY witness)
    (leftSame witness)
    (λ pairSame →
      rightSplitsLeftCollision witness (cong proj₂ pairSame))

crossCollisionMakesJointStrictOverRight :
  ∀ {State A B}
    {left : Observer.Observer State A}
    {right : Observer.Observer State B} →
  CrossCollision left right →
  Observer.StrictRefinement right (jointObserver left right)
crossCollisionMakesJointStrictOverRight {left = left} {right = right} witness =
  Observer.strictRefinement
    (jointRefinesRight left right)
    (rightCollisionX witness)
    (rightCollisionY witness)
    (rightSame witness)
    (λ pairSame →
      leftSplitsRightCollision witness (cong proj₁ pairSame))

------------------------------------------------------------------------
-- Leastness / universal property.
--
-- Any observer common that refines both left and right also refines their
-- pair.  Thus pairObserver is the least common refinement in the information
-- preorder induced by observational kernels.
------------------------------------------------------------------------

jointLeastCommonRefinement :
  ∀ {State A B Common}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B)
    (common : Observer.Observer State Common) →
  Observer.Refines left common →
  Observer.Refines right common →
  Observer.Refines (jointObserver left right) common
jointLeastCommonRefinement left right common commonRefinesLeft commonRefinesRight x y sameCommon =
  cong₂ _,_
    (commonRefinesLeft x y sameCommon)
    (commonRefinesRight x y sameCommon)

record LeastJointRefinement
    {State A B : Set}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) : Set₁ where
  constructor leastJointRefinement
  field
    joint : Observer.Observer State (A × B)
    leftBelowJoint : Observer.Refines left joint
    rightBelowJoint : Observer.Refines right joint
    least :
      ∀ {Common : Set}
        (common : Observer.Observer State Common) →
      Observer.Refines left common →
      Observer.Refines right common →
      Observer.Refines joint common

open LeastJointRefinement public

canonicalLeastJointRefinement :
  ∀ {State A B}
    (left : Observer.Observer State A)
    (right : Observer.Observer State B) →
  LeastJointRefinement left right
canonicalLeastJointRefinement left right =
  leastJointRefinement
    (jointObserver left right)
    (jointRefinesLeft left right)
    (jointRefinesRight left right)
    (jointLeastCommonRefinement left right)

record IncomparableObserverJoinBoundary : Set where
  field
    incomparableMeansEitherObserverIsInvalid : Bool
    crossCollisionsCanProveIncomparability : Bool
    pairObserverIsACommonRefinement : Bool
    pairObserverHasLeastCommonRefinementProperty : Bool
    joinAutomaticallySeparatesWholeState : Bool

canonicalIncomparableObserverJoinBoundary :
  IncomparableObserverJoinBoundary
canonicalIncomparableObserverJoinBoundary = record
  { incomparableMeansEitherObserverIsInvalid = false
  ; crossCollisionsCanProveIncomparability = true
  ; pairObserverIsACommonRefinement = true
  ; pairObserverHasLeastCommonRefinementProperty = true
  ; joinAutomaticallySeparatesWholeState = false
  }
