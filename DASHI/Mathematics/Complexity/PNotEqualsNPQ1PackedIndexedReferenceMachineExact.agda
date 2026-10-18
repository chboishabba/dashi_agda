module DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedIndexedReferenceMachineExact where

------------------------------------------------------------------------
-- FINITE GLOBALLY PACKED SHANNON REFERENCE MACHINE
--
-- A state is literally:
--   (remaining arity <= bound, complete truth-function index at that arity).
--
-- Because both coordinates have finite Fin carriers, no existential global
-- indexing or semantic oracle is assumed.
--
-- A nonterminal state has two total child transitions; zero arity is terminal.
-- This is an all-functions reference machine, not the minimal root-reachable
-- quotient and NOT a successful resource-charged Q1 constructor.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedTruthTableAutomatonExact as Indexed
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root

------------------------------------------------------------------------
-- Global IDs have an arity tag, preventing cross-layer accidental merging.
------------------------------------------------------------------------

data PackedIndexedState (bound : Nat) : Set where
  packed :
    (remaining : Fin.Fin (suc bound)) →
    Indexed.IndexedState (Fin.toℕ remaining) →
    PackedIndexedState bound

------------------------------------------------------------------------
-- A global transition is executable. At arity zero the state is terminal;
-- at positive arity it moves to the lower-arity canonical truth table.
------------------------------------------------------------------------

packedStep :
  ∀ {bound : Nat} →
  Bool →
  PackedIndexedState bound →
  Maybe (PackedIndexedState bound)
packedStep action (packed Fin.zero table) =
  nothing
packedStep action (packed (Fin.suc remaining) table) =
  just
    (packed remaining
      (Indexed.indexedStep action table))

packedFalseStep :
  ∀ {bound : Nat} →
  PackedIndexedState bound →
  Maybe (PackedIndexedState bound)
packedFalseStep =
  packedStep false

packedTrueStep :
  ∀ {bound : Nat} →
  PackedIndexedState bound →
  Maybe (PackedIndexedState bound)
packedTrueStep =
  packedStep true

------------------------------------------------------------------------
-- Both child targets are concrete and total on every nonterminal state.
------------------------------------------------------------------------

packedNonterminalStepExact :
  ∀ {bound : Nat}
    (remaining : Fin.Fin bound)
    (parent :
      Indexed.IndexedState (suc (Fin.toℕ remaining)))
    (action : Bool) →
  packedStep action
      (packed (Fin.suc remaining) parent)
  ≡
  just
    (packed remaining
      (Indexed.indexedStep action parent))
packedNonterminalStepExact remaining parent action =
  refl

packedTerminalStepExact :
  ∀ {bound : Nat}
    (state : Indexed.IndexedState zero)
    (action : Bool) →
  packedStep action (packed {bound = bound} Fin.zero state)
  ≡ nothing
packedTerminalStepExact state action =
  refl

------------------------------------------------------------------------
-- Exact initial state for any root formula.
------------------------------------------------------------------------

rootPackedState :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  PackedIndexedState rootVariables
rootPackedState {rootVariables = rootVariables} root =
  packed
    (Fin.fromℕ rootVariables)
    (Indexed.indexRestrictionNode
      (Root.rootLayerNode root))

------------------------------------------------------------------------
-- The total finite reference machine exists independently of any resource
-- budget. It is not a witness to the strict Q1 charged inequality. Construction
-- and operation costs must be separately charged, and the candidate-coupled
-- bound can legitimately reject this enormous all-functions automaton.
------------------------------------------------------------------------
