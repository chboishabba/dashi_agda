module DASHI.Mathematics.Complexity.PNotEqualsNPQ1PackedReachableMachineExact where

------------------------------------------------------------------------
-- DEPENDENT PACKING OF THE ACTUAL ROOT-REACHABLE NUMERIC QUOTIENT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1KeyOnlyTransitionExact as Key
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableTerminalAdmissionExact as Terminal
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth

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
packedArity (packed remaining path state) = remaining

rootPackedReachableState :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  PackedReachableState root
rootPackedReachableState {rootVariables} root =
  packed rootVariables Root.atRoot (Reachable.rootNumericState root)

rootPackedArityExact :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  packedArity (rootPackedReachableState root) ≡ rootVariables
rootPackedArityExact root = refl

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
  Truth.restrictTruthTable action
    (Reachable.decodeReachableState path source)
keyOnlyTargetExact action path source =
  proj₂ (proj₁ (Key.keyOnlyStepComplete action path source))

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
packedNonterminalArityDecreases action path state = refl

packedTerminalSelfLoop :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (action : Bool)
    (path : Root.DescentPath root zero)
    (state : Reachable.ReachableNumericState path) →
  packedReachableStep action (packed zero path state)
  ≡ packed zero path state
packedTerminalSelfLoop action path state = refl

packedTerminalLabel :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  PackedReachableState root →
  Maybe Bool
packedTerminalLabel (packed zero path state) =
  just (Terminal.reachableTerminalLabel path state)
packedTerminalLabel (packed (suc remaining) path state) = nothing

packedTerminalLabelExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (path : Root.DescentPath root zero)
    (state : Reachable.ReachableNumericState path) →
  packedTerminalLabel (packed zero path state)
  ≡ just (Terminal.reachableTerminalLabel path state)
packedTerminalLabelExact path state = refl

------------------------------------------------------------------------
-- Root-specific semantic packing is paid.  The remaining adapter is finite
-- global numbering of the canonical full-descent packed states.
------------------------------------------------------------------------
