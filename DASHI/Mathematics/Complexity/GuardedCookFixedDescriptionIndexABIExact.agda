module DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionIndexABIExact where

------------------------------------------------------------------------
-- FIXED-DESCRIPTION GENERATOR ABI: ONLY THE INDEX IS DYNAMIC
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as Costed

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
        | NatP.*-comm
            (Cost.fixedDescriptionBitStepConstant description)
            (suc index) =
  Cost.fixedDescriptionBitWorkByIndex description index

------------------------------------------------------------------------
-- FIREWALL / COMPILER CONSEQUENCE
--
-- The immutable `(machine,input,T)` description is compile-time data.  Runtime
-- calls carry only unary i; semantics reattach i with `atIndex`.  Therefore the
-- literal generator need not parse arbitrary coded machines or re-read its own
-- static description on every bit request.
------------------------------------------------------------------------
