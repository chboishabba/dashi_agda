module DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetFuelExact where

------------------------------------------------------------------------
-- B4 -> B6 SAME OBJECT: original strict 3*m <= remaining input length
-- guard supplies enough structurally decreasing fuel for the ACTUAL
-- binary-m-counted native signed raw-edge stream.
--
-- The original gamma source edge count and addresses may be huge;
-- no unary decoded count/addresses are executed by the native code.
-- The Nat inequalities/valueLE are strictly proof-side observations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact as Decisions
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountFuelOriginalExact as Fuel
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Original

-- Triple-budget source is at least as large as the actual edge count.
countAtMostThreeTimes :
  (m : Nat) →
  m ≤ (suc (suc (suc zero))) * m
countAtMostThreeTimes m =
  NatP.m≤m+n m (m + (m + zero))

-- This is a budget for source input LENGTH, not for the decoded Nat.
-- The actual bit-only budget result is transported via full numeric
-- correctness of the actual ripple adder/compareLE.
binaryBudgetSuppliesFuel :
  (mLE afterM : Word.BitWord) →
  Budget.binaryCountBudget mLE afterM ≡ true →
  Value.valueLE mLE ≤ length afterM
binaryBudgetSuppliesFuel mLE afterM allowed =
  NatP.≤-trans
    (countAtMostThreeTimes (Value.valueLE mLE))
    (Decisions.natBooleanLEWitness
      ((suc (suc (suc zero))) * Value.valueLE mLE)
      (length afterM)
      (trans (sym (Budget.binaryCountBudgetSameOriginal mLE afterM))
        allowed))

-- B6 core: successful original binary pre-loop 3*m budget buys
-- EXACT original counted signed raw-edge list and suffix after the
-- ACTUAL binary-decrement, input-length-fuel loop.
nativeBudgetedBinaryRawEdgesSameOriginal :
  (mLE afterM : Word.BitWord) →
  Budget.binaryCountBudget mLE afterM ≡ true →
  Edge.observeBinaryEdgeStream
    (Whole.readBinaryRawEdgesFuel (length afterM) mLE afterM)
  ≡ Original.readRawEdges (Value.valueLE mLE) afterM
nativeBudgetedBinaryRawEdgesSameOriginal mLE afterM permitted =
  Fuel.nativeBinaryCountFuelSameOriginal
    (length afterM) mLE afterM
    (binaryBudgetSuppliesFuel mLE afterM permitted)
