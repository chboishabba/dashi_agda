module DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact where

------------------------------------------------------------------------
-- EXACT COSTED STREAMED COOK-BIT ACCESS FOR ONE FIXED DESCRIPTION
--
-- The current Cook cursor uses one-hot local codecs, so its 2^w truth-table
-- factor is not uniform-polynomial when the queried machine itself varies.
-- Self-quotation fixes machine/input/T and varies only the requested bit index.
--
-- The path-exact costed cursor now gives the SAME returned bit and work count as
-- the actual streamed evaluator.  For one fixed description D:
--
--   work_D(i) <= (i + 1) * B_D
--             <= B_D * (queryBitLength(D,i) + 1),
--
-- where B_D is a machine/description constant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQueryLengthExact as QueryLength
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact as Stream
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingBitCostedExact as CostedBit

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

descriptionInitialTarget :
  (description : Description.GuardedCookFormulaDescription) →
  CNF.Bits
    (Decode.RowBitsWidth
      (descriptionMachine description)
      (descriptionCols description))
descriptionInitialTarget description =
  Sound.guardedInitialBits
    (Coded.codedStateCoverage (Description.code description))
    (Coded.codedSymbolCoverage (Description.code description))
    (Description.input description)
    (Description.steps description)

fixedDescriptionBitStepConstant :
  Description.GuardedCookFormulaDescription → Nat
fixedDescriptionBitStepConstant description =
  CostedBit.bitStepBudget
    (descriptionMachine description)
    (Description.steps description)
    (descriptionCols description)

streamedQueryBitCosted :
  (description : Description.GuardedCookFormulaDescription) →
  Nat →
  CostedBit.Costed (Maybe Bool)
streamedQueryBitCosted description index =
  CostedBit.streamedCookBitCosted
    (Coded.codedStateCoverage (Description.code description))
    (Coded.codedSymbolCoverage (Description.code description))
    (Description.nonemptyRules description)
    (Description.steps description)
    (descriptionCols description)
    (descriptionInitialTarget description)
    index

streamedQueryBitCostedResultExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  CostedBit.result (streamedQueryBitCosted description index)
  ≡ Stream.streamedQueryBit (Description.atIndex description index)
streamedQueryBitCostedResultExact description index =
  CostedBit.streamedCookBitCostedResultExact
    (Coded.codedStateCoverage (Description.code description))
    (Coded.codedSymbolCoverage (Description.code description))
    (Description.nonemptyRules description)
    (Description.steps description)
    (descriptionCols description)
    (descriptionInitialTarget description)
    index

streamedQueryBitCostedSemanticExact :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  CostedBit.result (streamedQueryBitCosted description index)
  ≡ Semantics.queryAnswer (Description.atIndex description index)
streamedQueryBitCostedSemanticExact description index =
  trans
    (streamedQueryBitCostedResultExact description index)
    (Stream.streamedQueryBitExact (Description.atIndex description index))

fixedDescriptionBitWork :
  Description.GuardedCookFormulaDescription → Nat → Nat
fixedDescriptionBitWork description index =
  CostedBit.work (streamedQueryBitCosted description index)

fixedDescriptionIndexBudget :
  Description.GuardedCookFormulaDescription → Nat → Nat
fixedDescriptionIndexBudget description index =
  suc index * fixedDescriptionBitStepConstant description

fixedDescriptionBitWorkByIndex :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  fixedDescriptionBitWork description index
  ≤ fixedDescriptionIndexBudget description index
fixedDescriptionBitWorkByIndex description index =
  CostedBit.streamedCookBitCostedWorkBound
    (Coded.codedStateCoverage (Description.code description))
    (Coded.codedSymbolCoverage (Description.code description))
    (Description.nonemptyRules description)
    (Description.steps description)
    (descriptionCols description)
    (descriptionInitialTarget description)
    index

fixedDescriptionLinearCoefficient :
  Description.GuardedCookFormulaDescription → Nat
fixedDescriptionLinearCoefficient = fixedDescriptionBitStepConstant

fixedDescriptionLinearBudget :
  Description.GuardedCookFormulaDescription → Nat → Nat
fixedDescriptionLinearBudget description queryLength =
  fixedDescriptionLinearCoefficient description * suc queryLength

indexSuccessorBelowQuerySuccessor :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  suc index
  ≤ suc (Query.queryBitLength (Description.atIndex description index))
indexSuccessorBelowQuerySuccessor description index =
  s≤s
    (QueryLength.indexBelowQueryBitLength
      (Description.atIndex description index))

indexBudgetBelowCanonicalLinearBudget :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  fixedDescriptionIndexBudget description index
  ≤ fixedDescriptionLinearBudget
      description
      (Query.queryBitLength (Description.atIndex description index))
indexBudgetBelowCanonicalLinearBudget description index =
  NatP.≤-trans
    (NatP.≤-reflexive
      (NatP.*-comm
        (suc index)
        (fixedDescriptionBitStepConstant description)))
    (NatP.*-monoˡ-≤
      (fixedDescriptionBitStepConstant description)
      (indexSuccessorBelowQuerySuccessor description index))

fixedDescriptionBitWorkLinearInCanonicalInput :
  (description : Description.GuardedCookFormulaDescription)
  (index : Nat) →
  fixedDescriptionBitWork description index
  ≤ fixedDescriptionLinearBudget
      description
      (Query.queryBitLength (Description.atIndex description index))
fixedDescriptionBitWorkLinearInCanonicalInput description index =
  NatP.≤-trans
    (fixedDescriptionBitWorkByIndex description index)
    (indexBudgetBelowCanonicalLinearBudget description index)

------------------------------------------------------------------------
-- FIREWALL
--
-- This theorem does NOT claim a uniform polynomial in a varying machine code.
-- With the current one-hot truth-table Cook constructor, 2^w_local depends on
-- machine cardinalities.  What is paid here is exactly the fixed-program case
-- needed by self-quotation: one immutable coded target, input and T, with only
-- the requested bit index varying.  The returned bit and charged work are now
-- produced by the same streamed recursion.
------------------------------------------------------------------------
