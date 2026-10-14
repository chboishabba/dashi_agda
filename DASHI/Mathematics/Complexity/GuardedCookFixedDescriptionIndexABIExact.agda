module DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionIndexABIExact where

------------------------------------------------------------------------
-- FIXED-DESCRIPTION GENERATOR ABI: ONLY THE INDEX IS DYNAMIC
--
-- In self-quotation, `(coded target, fixed input, T)` are compile-time constants.
-- Re-serialising/parsing them at every generated bit read is unnecessary.  The
-- runtime call payload may therefore be just unary i; semantics reattach i to
-- the immutable description using `Description.atIndex`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as Costed

------------------------------------------------------------------------
-- Unary runtime index code.  The terminator makes its literal length i+1.
------------------------------------------------------------------------

data IndexMark : Set where
  more : IndexMark
  stop : IndexMark

unaryIndex : Nat → List IndexMark
unaryIndex zero = stop ∷ []
unaryIndex (suc index) = more ∷ unaryIndex index

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

unaryIndexLengthExact :
  (index : Nat) →
  listLength (unaryIndex index) ≡ suc index
unaryIndexLengthExact zero = refl
unaryIndexLengthExact (suc index)
  rewrite unaryIndexLengthExact index = refl

------------------------------------------------------------------------
-- Index-only semantic request/result.
------------------------------------------------------------------------

indexRequestAnswer :
  Description.GuardedCookFormulaDescription →
  Nat → Maybe Bool
indexRequestAnswer description index =
  Semantics.queryAnswer (Description.atIndex description index)

indexRequestCosted :
  Description.GuardedCookFormulaDescription →
  Nat → Costed.Costed (Maybe Bool)
indexRequestCosted =
  Cost.streamedQueryBitCosted

indexRequestCostedSemanticExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Costed.result (indexRequestCosted description index)
  ≡ indexRequestAnswer description index
indexRequestCostedSemanticExact =
  Cost.streamedQueryBitCostedSemanticExact

------------------------------------------------------------------------
-- Work is linear directly in the dynamic unary-index payload.
------------------------------------------------------------------------

indexABIWorkBudget :
  Description.GuardedCookFormulaDescription →
  Nat → Nat
indexABIWorkBudget description index =
  Cost.fixedDescriptionBitStepConstant description
  * listLength (unaryIndex index)

indexABIWorkBound :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Costed.work (indexRequestCosted description index)
  ≤ indexABIWorkBudget description index
indexABIWorkBound description index
  rewrite unaryIndexLengthExact index
        | Agda.Builtin.Nat.*-comm
            (Cost.fixedDescriptionBitStepConstant description)
            (suc index) =
  Cost.fixedDescriptionBitWorkByIndex description index

------------------------------------------------------------------------
-- FIREWALL / COMPILER CONSEQUENCE
--
-- This is specialization, not compression by oracle: the immutable description
-- is already a fixed compile-time object and `atIndexOnlyChangesIndex` proves
-- queries vary only in i.  The eventual generator fragment therefore needs an
-- index ABI plus hard-wired finite tables/constants; it does not need a general
-- parser for arbitrary coded machines, inputs or T values.
------------------------------------------------------------------------
