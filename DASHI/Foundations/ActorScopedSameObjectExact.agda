module DASHI.Foundations.ActorScopedSameObjectExact where

------------------------------------------------------------------------
-- GENERIC ACTOR-SCOPED SAME-OBJECT RECOGNITION
--
-- DASHI contribution: extract the reusable representation-theoretic contract
-- exposed by the Monster-3B actor-scope audit.  No external theorem is claimed
-- here.  Source-backed Monster/Suzuki irreducibility facts remain owned by their
-- dedicated source modules; this file only states the generic formal condition
-- required before a carrier rechart may be promoted to a decomposition under a
-- declared actor.
--
-- A decomposition is therefore not a cardinality equation.  It consists of:
--   * one declared Actor type;
--   * actions of that SAME Actor on source and target carriers;
--   * two-sided carrier maps;
--   * an action-intertwining equation.
--
-- Changing Actor requires a fresh recognition.  Nothing below transports a
-- decomposition automatically from a subgroup/observer to a larger actor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- 1. Same-object recognition under one declared actor.
------------------------------------------------------------------------

record ActorScopedSameObject
    (Actor Source Target : Set)
    (sourceAction : Actor → Source → Source)
    (targetAction : Actor → Target → Target)
    : Set where
  constructor actor-scoped-same-object
  field
    toTarget : Source → Target
    fromTarget : Target → Source

    fromAfterTo :
      (state : Source) →
      fromTarget (toTarget state) ≡ state

    toAfterFrom :
      (state : Target) →
      toTarget (fromTarget state) ≡ state

    intertwinesAction :
      (actor : Actor) →
      (state : Source) →
      toTarget (sourceAction actor state)
      ≡ targetAction actor (toTarget state)

open ActorScopedSameObject public

------------------------------------------------------------------------
-- 2. Canonical action on a typed binary sum.
------------------------------------------------------------------------

sumAction :
  {Actor Left Right : Set} →
  (leftAction : Actor → Left → Left) →
  (rightAction : Actor → Right → Right) →
  Actor → Left ⊎ Right → Left ⊎ Right
sumAction leftAction rightAction actor (inj₁ left) =
  inj₁ (leftAction actor left)
sumAction leftAction rightAction actor (inj₂ right) =
  inj₂ (rightAction actor right)

------------------------------------------------------------------------
-- 3. Actor-scoped invariant binary decomposition.
--
-- This is the reusable formal surface for statements such as
--   E6-carrier ≃ F4-carrier ⊎ 26-carrier
-- only when BOTH summands are stable under the SAME declared actor.
------------------------------------------------------------------------

record ActorScopedSumDecomposition
    (Actor Whole Left Right : Set)
    (wholeAction : Actor → Whole → Whole)
    (leftAction : Actor → Left → Left)
    (rightAction : Actor → Right → Right)
    : Set where
  constructor actor-scoped-sum-decomposition
  field
    sameObject :
      ActorScopedSameObject
        Actor
        Whole
        (Left ⊎ Right)
        wholeAction
        (sumAction leftAction rightAction)

open ActorScopedSumDecomposition public

split :
  {Actor Whole Left Right : Set} →
  {wholeAction : Actor → Whole → Whole} →
  {leftAction : Actor → Left → Left} →
  {rightAction : Actor → Right → Right} →
  ActorScopedSumDecomposition
    Actor Whole Left Right wholeAction leftAction rightAction →
  Whole → Left ⊎ Right
split decomposition = toTarget (sameObject decomposition)

combine :
  {Actor Whole Left Right : Set} →
  {wholeAction : Actor → Whole → Whole} →
  {leftAction : Actor → Left → Left} →
  {rightAction : Actor → Right → Right} →
  ActorScopedSumDecomposition
    Actor Whole Left Right wholeAction leftAction rightAction →
  Left ⊎ Right → Whole
combine decomposition = fromTarget (sameObject decomposition)

combineAfterSplit :
  {Actor Whole Left Right : Set} →
  {wholeAction : Actor → Whole → Whole} →
  {leftAction : Actor → Left → Left} →
  {rightAction : Actor → Right → Right} →
  (decomposition :
    ActorScopedSumDecomposition
      Actor Whole Left Right wholeAction leftAction rightAction) →
  (state : Whole) →
  combine decomposition (split decomposition state) ≡ state
combineAfterSplit decomposition =
  fromAfterTo (sameObject decomposition)

splitAfterCombine :
  {Actor Whole Left Right : Set} →
  {wholeAction : Actor → Whole → Whole} →
  {leftAction : Actor → Left → Left} →
  {rightAction : Actor → Right → Right} →
  (decomposition :
    ActorScopedSumDecomposition
      Actor Whole Left Right wholeAction leftAction rightAction) →
  (state : Left ⊎ Right) →
  split decomposition (combine decomposition state) ≡ state
splitAfterCombine decomposition =
  toAfterFrom (sameObject decomposition)

splitIntertwinesSameActor :
  {Actor Whole Left Right : Set} →
  {wholeAction : Actor → Whole → Whole} →
  {leftAction : Actor → Left → Left} →
  {rightAction : Actor → Right → Right} →
  (decomposition :
    ActorScopedSumDecomposition
      Actor Whole Left Right wholeAction leftAction rightAction) →
  (actor : Actor) →
  (state : Whole) →
  split decomposition (wholeAction actor state)
  ≡ sumAction leftAction rightAction actor (split decomposition state)
splitIntertwinesSameActor decomposition =
  intertwinesAction (sameObject decomposition)

------------------------------------------------------------------------
-- 4. Machine-readable non-promotion boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    sameActorRequired : Bool
    twoSidedCarrierRecognitionRequired : Bool
    actionIntertwiningRequired : Bool
    cardinalitySplitPromotesToInvariantDecomposition : Bool
    decompositionAutomaticallySurvivesActorChange : Bool

open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true false false
