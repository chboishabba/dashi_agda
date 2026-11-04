module DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedPointOwnCookStreamingExact where

------------------------------------------------------------------------
-- BEHAVIOURAL FIXED-POINT QUOTATION -> SAME-OBJECT STREAMED OWN-COOK BITS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as Costed
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedPointOwnCookDescriptionExact as Own

recoveredOwnCookBit :
  Description.GuardedCookFormulaDescription →
  Nat →
  Maybe Bool
recoveredOwnCookBit description index =
  Stream.streamedQueryBit
    (Description.atIndex
      (Own.fixedPointRecoveredDescription description)
      index)

recoveredOwnCookBitExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  recoveredOwnCookBit description index
  ≡
  Semantics.queryAnswer
    (Description.atIndex description index)
recoveredOwnCookBitExact description index =
  Stream.streamedQueryBitExact
    (Description.atIndex
      (Own.fixedPointRecoveredDescription description)
      index)

recoveredOwnCookBitCosted :
  Description.GuardedCookFormulaDescription →
  Nat →
  Costed.Costed (Maybe Bool)
recoveredOwnCookBitCosted description index =
  Cost.streamedQueryBitCosted
    (Own.fixedPointRecoveredDescription description)
    index

recoveredOwnCookCostedSemanticExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  Costed.result (recoveredOwnCookBitCosted description index)
  ≡
  Semantics.queryAnswer
    (Description.atIndex description index)
recoveredOwnCookCostedSemanticExact description index =
  Cost.streamedQueryBitCostedSemanticExact
    (Own.fixedPointRecoveredDescription description)
    index

recoveredOwnCookWork :
  Description.GuardedCookFormulaDescription →
  Nat → Nat
recoveredOwnCookWork description index =
  Costed.work (recoveredOwnCookBitCosted description index)

recoveredOwnCookWorkByIndex :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  recoveredOwnCookWork description index
  ≤
  Cost.fixedDescriptionIndexBudget
    (Own.fixedPointRecoveredDescription description)
    index
recoveredOwnCookWorkByIndex description index =
  Cost.fixedDescriptionBitWorkByIndex
    (Own.fixedPointRecoveredDescription description)
    index

recoveredOwnCookLinearInCanonicalInput :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  recoveredOwnCookWork description index
  ≤
  Cost.fixedDescriptionLinearBudget
    (Own.fixedPointRecoveredDescription description)
    (Query.queryBitLength
      (Description.atIndex description index))
recoveredOwnCookLinearInCanonicalInput description index =
  Cost.fixedDescriptionBitWorkLinearInCanonicalInput
    (Own.fixedPointRecoveredDescription description)
    index

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The behavioural fixed-point quotation now drives the already-owned list-free
-- guarded-Cook bit evaluator for the SAME coded machine. Returned bits agree
-- with canonical query semantics and carry the same fixed-description linear
-- semantic work bound. Remaining work is operational compilation plus the final
-- same-object program-size/runtime/Cook resource fixed point.
------------------------------------------------------------------------
