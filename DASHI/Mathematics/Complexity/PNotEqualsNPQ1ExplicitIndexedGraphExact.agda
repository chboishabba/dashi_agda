module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact where

------------------------------------------------------------------------
-- FINITE, FULLY INDEXED SHANNON REFERENCE GRAPH
--
-- Enumerates EVERY truth-function state for every arity up to the chosen
-- bound. State IDs are the tagged Fin codes in PackedIndexedReferenceMachine.
-- Emits both transitions at all positive arities and one literal terminal
-- label at arity zero.
--
-- This makes no claim of minimality, cost feasibility, or a successful Q1
-- state constructor. The graph is intentionally enormous: its r-ary layer
-- has 2^(2^r) indices, not merely the root-reachable residual functions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (_++_; map; length)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedIndexedReferenceMachineExact as Packed
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Bits

------------------------------------------------------------------------
-- Enumerate the genuine Fin carrier, without postulated states.
------------------------------------------------------------------------

allFin : (n : Nat) → List (Fin.Fin n)
allFin zero = []
allFin (suc n) =
  Fin.zero ∷ map Fin.suc (allFin n)

data Listed {A : Set} (item : A) : List A → Set where
  first : ∀ {tail} → Listed item (item ∷ tail)
  later : ∀ {head tail} →
    Listed item tail →
    Listed item (head ∷ tail)

mapPreservesListed :
  ∀ {A B : Set}
    (f : A → B)
    {item : A}
    {source : List A} →
  Listed item source →
  Listed (f item) (map f source)
mapPreservesListed f first = first
mapPreservesListed f (later proof) =
  later (mapPreservesListed f proof)

allFinCovers :
  ∀ {n : Nat}
    (index : Fin.Fin n) →
  Listed index (allFin n)
allFinCovers {suc n} Fin.zero = first
allFinCovers {suc n} (Fin.suc index) =
  later
    (mapPreservesListed Fin.suc
      (allFinCovers index))

------------------------------------------------------------------------
-- Explicit finite key-index enumeration.
------------------------------------------------------------------------

allIndexedStates :
  (remaining : Nat) →
  List (Indexed.IndexedState remaining)
allIndexedStates remaining =
  allFin
    (Bits.bitCardinality
      (Bits.bitCardinality remaining))

allIndexedStatesCover :
  ∀ {remaining : Nat}
    (index : Indexed.IndexedState remaining) →
  Listed index (allIndexedStates remaining)
allIndexedStatesCover =
  allFinCovers

------------------------------------------------------------------------
-- Global packed state list. The arity tag prevents cross-layer collisions.
------------------------------------------------------------------------

statesAtArity :
  ∀ {bound : Nat} →
  (remaining : Fin.Fin (suc bound)) →
  List (Packed.PackedIndexedState bound)
statesAtArity remaining =
  map (Packed.packed remaining)
    (allIndexedStates (Fin.toℕ remaining))

concatMap :
  ∀ {A B : Set} →
  (A → List B) →
  List A →
  List B
concatMap f [] = []
concatMap f (item ∷ rest) =
  f item ++ concatMap f rest

allPackedStates :
  (bound : Nat) →
  List (Packed.PackedIndexedState bound)
allPackedStates bound =
  concatMap statesAtArity
    (allFin (suc bound))

------------------------------------------------------------------------
-- Each nonterminal index emits a literal pair of target IDs.
------------------------------------------------------------------------

record EmittedTransition
    (bound : Nat) : Set where
  constructor emitted-transition
  field
    source : Packed.PackedIndexedState bound
    falseTarget : Packed.PackedIndexedState bound
    trueTarget : Packed.PackedIndexedState bound

open EmittedTransition public

emitTransition :
  ∀ {bound : Nat}
    (remaining : Fin.Fin bound)
    (index :
      Indexed.IndexedState (suc (Fin.toℕ remaining))) →
  EmittedTransition bound
emitTransition remaining index =
  emitted-transition
    (Packed.packed (Fin.suc remaining) index)
    (Packed.packed remaining
      (Indexed.indexedStep false index))
    (Packed.packed remaining
      (Indexed.indexedStep true index))

transitionsAtArity :
  ∀ {bound : Nat} →
  (remaining : Fin.Fin bound) →
  List (EmittedTransition bound)
transitionsAtArity remaining =
  map (emitTransition remaining)
    (allIndexedStates (suc (Fin.toℕ remaining)))

allEmittedTransitions :
  (bound : Nat) →
  List (EmittedTransition bound)
allEmittedTransitions bound =
  concatMap transitionsAtArity
    (allFin bound)

------------------------------------------------------------------------
-- A terminal at arity zero has a literal stored Boolean label.
------------------------------------------------------------------------

record EmittedTerminal
    (bound : Nat) : Set where
  constructor emitted-terminal
  field
    state : Packed.PackedIndexedState bound
    label : Bool

open EmittedTerminal public

emitTerminal :
  ∀ {bound : Nat} →
  Indexed.IndexedState zero →
  EmittedTerminal bound
emitTerminal index =
  emitted-terminal
    (Packed.packed Fin.zero index)
    (Indexed.terminalLabel index)

allEmittedTerminals :
  (bound : Nat) →
  List (EmittedTerminal bound)
allEmittedTerminals bound =
  map emitTerminal (allIndexedStates zero)

------------------------------------------------------------------------
-- An explicit graph is constructed by computation for any bound.
------------------------------------------------------------------------

record ReferenceGraph (bound : Nat) : Set where
  constructor reference-graph
  field
    states : List (Packed.PackedIndexedState bound)
    transitions : List (EmittedTransition bound)
    terminals : List (EmittedTerminal bound)

open ReferenceGraph public

buildReferenceGraph :
  (bound : Nat) →
  ReferenceGraph bound
buildReferenceGraph bound =
  reference-graph
    (allPackedStates bound)
    (allEmittedTransitions bound)
    (allEmittedTerminals bound)

------------------------------------------------------------------------
-- Admission at a source state is operationally exact: the explicit targets
-- agree with the packed machine's two step results.
------------------------------------------------------------------------

emittedFalseTargetExact :
  ∀ {bound : Nat}
    (remaining : Fin.Fin bound)
    (index :
      Indexed.IndexedState (suc (Fin.toℕ remaining))) →
  Packed.packedStep false
    (source (emitTransition remaining index))
  ≡
  Agda.Builtin.Maybe.just
    (falseTarget (emitTransition remaining index))
emittedFalseTargetExact remaining index =
  refl

emittedTrueTargetExact :
  ∀ {bound : Nat}
    (remaining : Fin.Fin bound)
    (index :
      Indexed.IndexedState (suc (Fin.toℕ remaining))) →
  Packed.packedStep true
    (source (emitTransition remaining index))
  ≡
  Agda.Builtin.Maybe.just
    (trueTarget (emitTransition remaining index))
emittedTrueTargetExact remaining index =
  refl

------------------------------------------------------------------------
-- This graph contains every possible Boolean function at each layer. It is
-- not the canonical root-reachable quotient and does not yield a polynomial
-- constructor. In particular graph existence and constructor budget success
-- are deliberately independent.
------------------------------------------------------------------------
