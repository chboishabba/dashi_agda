{-# OPTIONS --safe #-}
module DASHI.Core.AtomicGlobalFibreLiftExact where

------------------------------------------------------------------------
-- FIBRE-NATIVE ATOMIC -> GLOBAL EQUALITY LIFT
--
-- An atomic theorem is not promoted to a global theorem merely because it is
-- true at each fibre coordinate.  The global observer/aggregator must own the
-- receipt that it preserves pointwise equality.  Once that receipt exists, the
-- large fibre carrier stays opaque: global consumers receive only equality of
-- observer outputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

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
-- Ordinary functions are the degenerate one-coordinate fibre observer.
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
    globalObserverMustReopenAtomicRepresentation : Bool
    pointwiseProofMayRemainOpaqueAfterLift : Bool

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalAtomicGlobalFibreBoundary : AtomicGlobalFibreBoundary
canonicalAtomicGlobalFibreBoundary =
  atomic-global-fibre-boundary false true false true
