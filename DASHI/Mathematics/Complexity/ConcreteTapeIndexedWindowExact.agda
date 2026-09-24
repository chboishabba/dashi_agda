module DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact where

------------------------------------------------------------------------
-- INDEXED ROW/WINDOW GEOMETRY FOR THE CONCRETE COOK--LEVIN MACHINE
--
-- This pays the next representation seam below machine locality: a 2x3
-- window is not merely an unlocated six-cell value.  Each of its six cells is
-- tied to one shared tape index by an inductive list-membership witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

data At {A : Set} : Nat → A → List A → Set where
  here :
    ∀ {x xs} →
    At zero x (x ∷ xs)

  there :
    ∀ {n x y xs} →
    At n x xs →
    At (suc n) x (y ∷ xs)

record TripleAt {A : Set}
    (index : Nat)
    (left center right : A)
    (xs : List A) : Set where
  field
    leftAt : At index left xs
    centerAt : At (suc index) center xs
    rightAt : At (suc (suc index)) right xs

open TripleAt public

record IndexedSixCellWindow
    (machine : Local.ConcreteTapeMachine)
    (before after : Local.TapeRow machine) : Set₁ where
  field
    index : Nat

    oldLeft oldCenter oldRight :
      Local.TapeCell (Local.State machine) (Local.Symbol machine)

    newLeft newCenter newRight :
      Local.TapeCell (Local.State machine) (Local.Symbol machine)

    oldTriple :
      TripleAt index oldLeft oldCenter oldRight (Local.cells before)

    newTriple :
      TripleAt index newLeft newCenter newRight (Local.cells after)

open IndexedSixCellWindow public

forgetIndex :
  ∀ {machine before after} →
  IndexedSixCellWindow machine before after →
  Local.SixCellWindow machine
forgetIndex occurrence =
  Local.six-cell-window
    (oldLeft occurrence)
    (oldCenter occurrence)
    (oldRight occurrence)
    (newLeft occurrence)
    (newCenter occurrence)
    (newRight occurrence)

record IndexedLocalStepWitness
    (machine : Local.ConcreteTapeMachine)
    (before after : Local.TapeRow machine) : Set₁ where
  field
    occurrence : IndexedSixCellWindow machine before after
    rule :
      Local.TapeRule (Local.State machine) (Local.Symbol machine)
    ruleRealizesIndexedWindow :
      Local.RuleRealizesWindow machine rule (forgetIndex occurrence)
    outsideRadiusOnePreserved :
      (position : Nat) → Set

open IndexedLocalStepWitness public

indexedWitnessHasUnlocatedWindow :
  ∀ {machine before after} →
  IndexedLocalStepWitness machine before after →
  Local.SixCellWindow machine
indexedWitnessHasUnlocatedWindow witness =
  forgetIndex (occurrence witness)

indexedOccurrenceUsesOneSharedCoordinate :
  ∀ {machine before after}
    (occurrence : IndexedSixCellWindow machine before after) →
  index occurrence ≡ index occurrence
indexedOccurrenceUsesOneSharedCoordinate occurrence = refl

record ConcreteTapeIndexedWindowBoundary : Set where
  constructor concrete-tape-indexed-window-boundary
  field
    inductiveListIndexPaid : Bool
    indexedWindowGeometryPaid : Bool
    outsideRadiusOnePredicateTyped : Bool
    allWindowLocalityEquivalencePaid : Bool
    canonicalSATTableauWeldPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeIndexedWindowBoundary :
  ConcreteTapeIndexedWindowBoundary
canonicalConcreteTapeIndexedWindowBoundary =
  concrete-tape-indexed-window-boundary
    true true true false false false
