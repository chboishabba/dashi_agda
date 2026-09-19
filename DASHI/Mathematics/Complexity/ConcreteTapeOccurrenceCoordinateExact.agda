module DASHI.Mathematics.Complexity.ConcreteTapeOccurrenceCoordinateExact where

------------------------------------------------------------------------
-- CONTIGUOUS REWRITE -> EXACT GLOBAL TAPE COORDINATE
--
-- A WindowRewriteOccurrence carries one common prefix.  Its length is exactly
-- the left coordinate of the changed 3-cell neighborhood.  This module proves
-- that statement against the inductive At/TripleAt geometry, removing the
-- previous existential/location gap for the distinguished transition window.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeIndexedWindowExact as Indexed

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

tripleAfterPrefix :
  ∀ {A : Set}
    (prefix : List A)
    (left center right : A)
    (suffix : List A) →
  Indexed.TripleAt
    (listLength prefix)
    left center right
    (Local.append prefix (left ∷ center ∷ right ∷ suffix))
tripleAfterPrefix [] left center right suffix = record
  { Indexed.leftAt = Indexed.here
  ; Indexed.centerAt = Indexed.there Indexed.here
  ; Indexed.rightAt = Indexed.there (Indexed.there Indexed.here)
  }
tripleAfterPrefix (x ∷ prefix) left center right suffix
    with tripleAfterPrefix prefix left center right suffix
... | rest = record
  { Indexed.leftAt = Indexed.there (Indexed.leftAt rest)
  ; Indexed.centerAt = Indexed.there (Indexed.centerAt rest)
  ; Indexed.rightAt = Indexed.there (Indexed.rightAt rest)
  }

transportTriple :
  ∀ {A : Set} {index : Nat} {left center right : A} {xs ys : List A} →
  xs ≡ ys →
  Indexed.TripleAt index left center right xs →
  Indexed.TripleAt index left center right ys
transportTriple refl triple = triple

occurrenceToIndexedWindow :
  ∀ {machine before after window} →
  Local.WindowRewriteOccurrence machine before after window →
  Indexed.IndexedSixCellWindow machine before after
occurrenceToIndexedWindow {window = window} occurrence = record
  { Indexed.index = listLength (Local.prefix occurrence)
  ; Indexed.oldLeft = Local.oldLeft window
  ; Indexed.oldCenter = Local.oldCenter window
  ; Indexed.oldRight = Local.oldRight window
  ; Indexed.newLeft = Local.newLeft window
  ; Indexed.newCenter = Local.newCenter window
  ; Indexed.newRight = Local.newRight window
  ; Indexed.oldTriple =
      transportTriple
        (sym (Local.beforeShape occurrence))
        (tripleAfterPrefix
          (Local.prefix occurrence)
          (Local.oldLeft window)
          (Local.oldCenter window)
          (Local.oldRight window)
          (Local.suffix occurrence))
  ; Indexed.newTriple =
      transportTriple
        (sym (Local.afterShape occurrence))
        (tripleAfterPrefix
          (Local.prefix occurrence)
          (Local.newLeft window)
          (Local.newCenter window)
          (Local.newRight window)
          (Local.suffix occurrence))
  }

forgetOccurrenceCoordinate :
  ∀ {machine before after window}
    (occurrence : Local.WindowRewriteOccurrence machine before after window) →
  Indexed.forgetIndex (occurrenceToIndexedWindow occurrence) ≡ window
forgetOccurrenceCoordinate {window = Local.six-cell-window _ _ _ _ _ _}
    occurrence = refl

machineStepHasExactTransitionCoordinate :
  ∀ {machine before after} →
  Local.MachineStep machine before after →
  Indexed.IndexedSixCellWindow machine before after
machineStepHasExactTransitionCoordinate step =
  occurrenceToIndexedWindow (Local.occurrence step)

machineStepIndexedWindowIsRuleWindow :
  ∀ {machine before after}
    (step : Local.MachineStep machine before after) →
  Indexed.forgetIndex (machineStepHasExactTransitionCoordinate step)
  ≡ Local.window step
machineStepIndexedWindowIsRuleWindow step =
  forgetOccurrenceCoordinate (Local.occurrence step)

record ConcreteTapeOccurrenceCoordinateBoundary : Set where
  constructor concrete-tape-occurrence-coordinate-boundary
  field
    prefixLengthIndexingPaid : Bool
    rewriteCoordinateDerivationPaid : Bool
    machineStepDistinguishedWindowLocated : Bool
    allOverlappingWindowsCharacterized : Bool
    canonicalSATTableauWeldPaid : Bool
    pVsNPResolved : Bool

canonicalConcreteTapeOccurrenceCoordinateBoundary :
  ConcreteTapeOccurrenceCoordinateBoundary
canonicalConcreteTapeOccurrenceCoordinateBoundary =
  concrete-tape-occurrence-coordinate-boundary
    true true true false false false
