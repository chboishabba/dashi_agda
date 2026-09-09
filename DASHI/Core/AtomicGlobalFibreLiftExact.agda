{-# OPTIONS --safe #-}
module DASHI.Core.AtomicGlobalFibreLiftExact where

------------------------------------------------------------------------
-- FIBRE-NATIVE ATOMIC -> GLOBAL OBSERVER LIFTS
--
-- An atomic theorem is not promoted to a global theorem merely because it is
-- true at each fibre coordinate.  The global observer/aggregator must own the
-- receipt that it preserves the relation consumed downstream.  Once that
-- receipt exists, the large fibre carrier stays opaque: global consumers see
-- only observer outputs and the lifted relation between them.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Equality-preserving observer.
------------------------------------------------------------------------

record FibreObserverLift
  {Index Atomic Global : Set}
  (observe : (Index → Atomic) → Global)
  : Set where
  constructor fibre-observer-lift
  field
    preservesPointwiseEquality :
      ∀ {left right : Index → Atomic} →
      (∀ i → left i ≡ right i) →
      observe left ≡ observe right

open FibreObserverLift public

atomicFamilyToGlobal :
  ∀ {Index Atomic Global : Set}
    {observe : (Index → Atomic) → Global} →
  FibreObserverLift observe →
  {left right : Index → Atomic} →
  (∀ i → left i ≡ right i) →
  observe left ≡ observe right
atomicFamilyToGlobal lift atomic =
  preservesPointwiseEquality lift atomic

------------------------------------------------------------------------
-- Relation-preserving observer.
--
-- Equality is only one consumer.  Inequalities, refinement orders and other
-- fibre-local relations can be lifted too, but only when the observer carries
-- the corresponding preservation receipt.  This is the native fibre form of
-- "atomic proof -> observed/global proof" and prevents an unsafe generic
-- local-to-global promotion rule.
------------------------------------------------------------------------

record FibreRelationLift
  {Index Atomic Global : Set}
  (AtomicRel : Atomic → Atomic → Set)
  (GlobalRel : Global → Global → Set)
  (observe : (Index → Atomic) → Global)
  : Set where
  constructor fibre-relation-lift
  field
    preservesPointwiseRelation :
      ∀ {left right : Index → Atomic} →
      (∀ i → AtomicRel (left i) (right i)) →
      GlobalRel (observe left) (observe right)

open FibreRelationLift public

atomicRelationFamilyToGlobal :
  ∀ {Index Atomic Global : Set}
    {AtomicRel : Atomic → Atomic → Set}
    {GlobalRel : Global → Global → Set}
    {observe : (Index → Atomic) → Global} →
  FibreRelationLift AtomicRel GlobalRel observe →
  {left right : Index → Atomic} →
  (∀ i → AtomicRel (left i) (right i)) →
  GlobalRel (observe left) (observe right)
atomicRelationFamilyToGlobal lift atomic =
  preservesPointwiseRelation lift atomic

------------------------------------------------------------------------
-- Ordinary functions are the degenerate one-coordinate/coarse observer.
------------------------------------------------------------------------

mapEquality :
  ∀ {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
mapEquality f refl = refl

------------------------------------------------------------------------
-- Epistemic / elaboration boundary.
------------------------------------------------------------------------

record AtomicGlobalFibreBoundary : Set where
  constructor atomic-global-fibre-boundary
  field
    atomicTruthAloneCreatesGlobalTruth : Bool
    observerPreservationReceiptRequired : Bool
    relationSpecificPreservationRequired : Bool
    globalObserverMustReopenAtomicRepresentation : Bool
    pointwiseProofMayRemainOpaqueAfterLift : Bool
    solverMayNormalizeThroughFibreBoundary : Bool

canonicalAtomicGlobalFibreBoundary : AtomicGlobalFibreBoundary
canonicalAtomicGlobalFibreBoundary =
  atomic-global-fibre-boundary false true true false true false
