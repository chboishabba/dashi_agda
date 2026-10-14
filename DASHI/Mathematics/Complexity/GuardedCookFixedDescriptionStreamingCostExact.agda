module DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact where

------------------------------------------------------------------------
-- FIXED-DESCRIPTION POLYNOMIAL ENVELOPE FOR STREAMED COOK-BIT ACCESS
--
-- The current Cook cursor uses one-hot local codecs, so its 2^w truth-table
-- factor is not uniform-polynomial when the queried machine itself varies.
-- Self-quotation does not require that stronger statement: machine/input/T are
-- immutable and only the bit index varies.
--
-- For one fixed GuardedCookFormulaDescription, the entire clause-seek budget is
-- therefore a constant C_D.  A conservative bit cursor may perform at most one
-- clause seek per consumed bit, hence
--
--   W_D(i) = C_D * (i + 1)
--          <= C_D * (queryBitLength(D,i) + 1).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQueryLengthExact as QueryLength
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostExact as ClauseCost

------------------------------------------------------------------------
-- Same fixed concrete machine / guarded width for every query index.
------------------------------------------------------------------------

descriptionMachine :
  Description.GuardedCookFormulaDescription →
  Local.ConcreteTapeMachine
descriptionMachine description =
  Presented.finitePresentedStandardToConcrete
    (Coded.decodeCodedStandardTM (Description.code description))

descriptionCols :
  (description : Description.GuardedCookFormulaDescription) → Nat
descriptionCols description =
  Guard.guardedInitialCols
    (Description.input description)
    (Description.steps description)

fixedClauseSeekConstant :
  Description.GuardedCookFormulaDescription → Nat
fixedClauseSeekConstant description =
  suc
    (ClauseCost.globalClauseSeekWorkBudget
      (descriptionMachine description)
      (Description.steps description)
      (descriptionCols description))

------------------------------------------------------------------------
-- Conservative streamed-bit work.  The `suc` protects the zero-work cases and
-- absorbs token/cursor bookkeeping at this semantic cost layer.
------------------------------------------------------------------------

fixedDescriptionBitWork :
  Description.GuardedCookFormulaDescription → Nat → Nat
fixedDescriptionBitWork description index =
  fixedClauseSeekConstant description * suc index

fixedDescriptionQueryWork :
  (description : Description.GuardedCookFormulaDescription) → Nat → Nat
fixedDescriptionQueryWork description index =
  fixedClauseSeekConstant description
  * suc (Query.queryBitLength (Description.atIndex description index))

indexSuccessorBelowQuerySuccessor :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  suc index
  ≤ suc (Query.queryBitLength (Description.atIndex description index))
indexSuccessorBelowQuerySuccessor description index =
  s≤s
    (QueryLength.indexBelowQueryBitLength
      (Description.atIndex description index))

fixedDescriptionBitWorkPolynomial :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  fixedDescriptionBitWork description index
  ≤ fixedDescriptionQueryWork description index
fixedDescriptionBitWorkPolynomial description index =
  NatP.*-monoˡ-≤
    (fixedClauseSeekConstant description)
    (indexSuccessorBelowQuerySuccessor description index)

------------------------------------------------------------------------
-- Degree-one polynomial presentation in the exact canonical query-code length.
------------------------------------------------------------------------

fixedDescriptionLinearCoefficient :
  Description.GuardedCookFormulaDescription → Nat
fixedDescriptionLinearCoefficient = fixedClauseSeekConstant

fixedDescriptionLinearBudget :
  Description.GuardedCookFormulaDescription → Nat → Nat
fixedDescriptionLinearBudget description queryLength =
  fixedDescriptionLinearCoefficient description * suc queryLength

fixedDescriptionBitWorkLinearInCanonicalInput :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  fixedDescriptionBitWork description index
  ≤ fixedDescriptionLinearBudget
      description
      (Query.queryBitLength (Description.atIndex description index))
fixedDescriptionBitWorkLinearInCanonicalInput =
  fixedDescriptionBitWorkPolynomial

------------------------------------------------------------------------
-- FIREWALL
--
-- This theorem does NOT claim a uniform polynomial in a varying machine code.
-- With the current one-hot truth-table Cook constructor, `2^w_local` depends on
-- machine cardinalities.  What is paid here is exactly the fixed-program case
-- needed by self-quotation: one immutable coded target, input and T, with only
-- the requested bit index varying.
------------------------------------------------------------------------
