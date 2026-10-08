module DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedReachableMachineExact where

------------------------------------------------------------------------
-- DEPENDENT PACKING OF THE ACTUAL ROOT-REACHABLE NUMERIC QUOTIENT
--
-- This is the root-specific analogue of PackedIndexedReferenceMachineExact.
-- The all-functions truth-state supergraph is not used.
--
-- A packed state contains:
--   * its actual remaining arity;
--   * the canonical root descent path to that layer;
--   * a Fin index into exactly the deduplicated keys reachable from the root.
--
-- Nonterminal transitions use KeyOnlyTransitionExact and therefore require no
-- representative reconstruction at runtime. Terminal states self-loop only to
-- make the carrier total; Shannon actions are semantically inadmissible there.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1KeyOnlyTransitionExact as Key
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableTerminalAdmissionExact as Terminal

------------------------------------------------------------------------
-- One dependent packed root-reachable state.
------------------------------------------------------------------------

data PackedReachableState
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set where
  packed :
    (remaining : Nat) →
    (path : Root.DescentPath root remaining) →
    Reachable.ReachableNumericState path →
    PackedReachableState root

packedArity :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  PackedReachableState root →
  Nat
packedArity (packed remaining path state) =
  remaining

rootPackedReachableState :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  PackedReachableState root
rootPackedReachableState {rootVariables} root =
  packed
    rootVariables
    Root.atRoot
    (Reachable.rootNumericState root)

rootPackedArityExact :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  packedArity (rootPackedReachableState root)
  ≡ rootVariables
rootPackedArityExact root =
  refl

------------------------------------------------------------------------
-- Extract the total target proved to exist by key-only search completeness.
------------------------------------------------------------------------

keyOnlyTarget :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (path : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState path) →
  Reachable.ReachableNumericState (Root.descend path)
keyOnlyTarget action path source =
  proj₁ (proj₁ (Key.keyOnlyStepComplete action path source))

keyOnlyTargetExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (path : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState path) →
  Reachable.decodeReachableState
    (Root.descend path)
    (keyOnlyTarget action path source)
  ≡
  DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact.restrictTruthTable
    action
    (Reachable.decodeReachableState path source)
keyOnlyTargetExact action path source =
  proj₂ (proj₁ (Key.keyOnlyStepComplete action path source))

------------------------------------------------------------------------
-- Executable total packed transition.
------------------------------------------------------------------------

packedReachableStep :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Bool →
  PackedReachableState root →
  PackedReachableState root
packedReachableStep action (packed zero path state) =
  packed zero path state
packedReachableStep action (packed (suc remaining) path state) =
  packed
    remaining
    (Root.descend path)
    (keyOnlyTarget action path state)

packedNonterminalArityDecreases :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (path : Root.DescentPath root (suc remaining))
    (state : Reachable.ReachableNumericState path) →
  packedArity
    (packedReachableStep action
      (packed (suc remaining) path state))
  ≡ remaining
packedNonterminalArityDecreases action path state =
  refl

packedTerminalSelfLoop :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (path : Root.DescentPath root zero)
    (state : Reachable.ReachableNumericState path) →
  packedReachableStep action (packed zero path state)
  ≡ packed zero path state
packedTerminalSelfLoop action path state =
  refl

------------------------------------------------------------------------
-- Computed terminal observation.
------------------------------------------------------------------------

packedTerminalLabel :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  PackedReachableState root →
  Maybe Bool
packedTerminalLabel (packed zero path state) =
  just (Terminal.reachableTerminalLabel path state)
packedTerminalLabel (packed (suc remaining) path state) =
  nothing

packedTerminalLabelExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root zero)
    (state : Reachable.ReachableNumericState path) →
  packedTerminalLabel (packed zero path state)
  ≡ just (Terminal.reachableTerminalLabel path state)
packedTerminalLabelExact path state =
  refl

------------------------------------------------------------------------
-- MAX-CUT STATUS
--
-- Root-specific packing at the semantic carrier level is now paid:
--   * no all-functions states;
--   * executable key-only transitions;
--   * root arity by construction;
--   * one-step arity decrement by construction;
--   * computed terminal labels.
--
-- Remaining mechanical adapter:
-- enumerate all PackedReachableState values along the unique full descent and
-- assign one global Fin index, preserving these exact transitions/labels.
------------------------------------------------------------------------
