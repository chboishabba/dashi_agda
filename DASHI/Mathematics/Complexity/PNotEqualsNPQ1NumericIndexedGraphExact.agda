module DASHI.Mathematics.Complexity.PNotEqualsNPQ1NumericIndexedGraphExact where

------------------------------------------------------------------------
-- SINGLE FIN-INDEXED SHANNON AUTOMATON
--
-- Convert the explicitly enumerated, arity-tagged truth-function states into
-- one global numerical Fin carrier of length (allPackedStates bound).
--
-- No quotient representative, semantic oracle, or indexing function is
-- postulated. Each reachable packed state is located constructively using
-- the coverage proof from ExplicitIndexedGraphExact, and the corresponding
-- global index is the position of that witness in the emitted state list.
--
-- The machine is deliberately the ALL-FUNCTIONS reference graph, not the
-- canonical reachable minimum and not a strict-budget Q1 witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Fin.Base as Fin
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedIndexedReferenceMachineExact as Packed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact as Graph
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed

------------------------------------------------------------------------
-- Convert a proved list occurrence into its actual Fin position.
------------------------------------------------------------------------

listedPosition :
  ∀ {A : Set} {item : A} {items : List A} →
  Graph.Listed item items →
  Fin.Fin (length items)
listedPosition Graph.first =
  Fin.zero
listedPosition (Graph.later rest) =
  Fin.suc (listedPosition rest)

lookupAt :
  ∀ {A : Set}
    (items : List A) →
  Fin.Fin (length items) →
  A
lookupAt [] ()
lookupAt (head ∷ tail) Fin.zero =
  head
lookupAt (head ∷ tail) (Fin.suc index) =
  lookupAt tail index

lookupAtListedPosition :
  ∀ {A : Set} {item : A} {items : List A}
    (proof : Graph.Listed item items) →
  lookupAt items (listedPosition proof)
  ≡ item
lookupAtListedPosition Graph.first =
  refl
lookupAtListedPosition (Graph.later rest) =
  lookupAtListedPosition rest

------------------------------------------------------------------------
-- One globally numbered state carrier for all arities up to bound.
------------------------------------------------------------------------

NumericState :
  Nat → Set
NumericState bound =
  Fin.Fin
    (length (Graph.allPackedStates bound))

numericEncode :
  ∀ {bound : Nat} →
  Packed.PackedIndexedState bound →
  NumericState bound
numericEncode (Packed.packed remaining index) =
  listedPosition
    (Graph.allPackedStatesCover remaining index)

numericDecode :
  ∀ {bound : Nat} →
  NumericState bound →
  Packed.PackedIndexedState bound
numericDecode {bound = bound} =
  lookupAt (Graph.allPackedStates bound)

numericDecodeEncode :
  ∀ {bound : Nat}
    (state : Packed.PackedIndexedState bound) →
  numericDecode (numericEncode state)
  ≡ state
numericDecodeEncode (Packed.packed remaining index) =
  lookupAtListedPosition
    (Graph.allPackedStatesCover remaining index)

------------------------------------------------------------------------
-- All numerical edges are literally induced by the packed Shannon machine.
------------------------------------------------------------------------

mapMaybe :
  ∀ {A B : Set} →
  (A → B) →
  Maybe A →
  Maybe B
mapMaybe f nothing =
  nothing
mapMaybe f (just value) =
  just (f value)

numericStep :
  ∀ {bound : Nat} →
  Bool →
  NumericState bound →
  Maybe (NumericState bound)
numericStep action index =
  mapMaybe numericEncode
    (Packed.packedStep action
      (numericDecode index))

numericStepOnEncodedStateExact :
  ∀ {bound : Nat}
    (action : Bool)
    (state : Packed.PackedIndexedState bound) →
  numericStep action (numericEncode state)
  ≡
  mapMaybe numericEncode
    (Packed.packedStep action state)
numericStepOnEncodedStateExact action state
    rewrite numericDecodeEncode state =
  refl

------------------------------------------------------------------------
-- Real terminal-label lookup on globally numbered states.
------------------------------------------------------------------------

numericTerminalLabel :
  ∀ {bound : Nat} →
  NumericState bound →
  Maybe Bool
numericTerminalLabel index
    with numericDecode index
... | Packed.packed Fin.zero terminal =
  just (Indexed.terminalLabel terminal)
... | Packed.packed (Fin.suc remaining) nonterminal =
  nothing

numericTerminalLabelOnEncodedZeroState :
  ∀ {bound : Nat}
    (state : Indexed.IndexedState zero) →
  numericTerminalLabel
    (numericEncode
      (Packed.packed {bound = bound} Fin.zero state))
  ≡
  just (Indexed.terminalLabel state)
numericTerminalLabelOnEncodedZeroState state
    rewrite numericDecodeEncode
      (Packed.packed Fin.zero state) =
  refl

------------------------------------------------------------------------
-- We now have a real finite numerical stateCount, two numerical transitions,
-- and a literal terminal-label function. The source-level decoding theorem
-- prevents fabricated state indices or changing the underlying Shannon object.
--
-- Still outstanding: finite root-REACHABLE quotient/minimal numbering,
-- selected-state rewrite admission, faithful interpreter-step cost, exact Q1
-- all-overhead strict fit, and non-circular candidate-root success.
------------------------------------------------------------------------
