module DASHI.Mathematics.Complexity.PNotEqualsNPFixedDescriptionCookBitGeneratorExact where

------------------------------------------------------------------------
-- FIXED-DESCRIPTION GUARDED-COOK BIT GENERATOR
--
-- The diagonal does not require one polynomial generator uniform over arbitrary
-- machine codes.  Its own coded target is fixed.  We therefore freeze one
-- GuardedCookFormulaDescription and vary only the requested index.
--
-- This is the correct asymptotic surface: local Cook window width / truth-table
-- width are constants of the fixed target program rather than growing inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookStreamingBitExact as Streaming
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

queryPolynomialBudget :
  Nat → Nat →
  Description.GuardedCookFormulaDescription →
  Nat → Nat
queryPolynomialBudget coefficient degree description index =
  coefficient
  * Clock.natPower
      (suc (Query.queryBitLength (Description.atIndex description index)))
      degree

maybeOutputState :
  ∀ {State : Set} →
  State → State → State → Agda.Builtin.Maybe.Maybe Bool → State
maybeOutputState none falseState trueState nothing = none
maybeOutputState none falseState trueState (just false) = falseState
maybeOutputState none falseState trueState (just true) = trueState

record FixedDescriptionCookBitGenerator
    (description : Description.GuardedCookFormulaDescription)
    (presentation : Presented.FinitePresentedStandardTM) : Set₂ where
  field
    zeroSymbol : Presented.Symbol presentation
    oneSymbol : Presented.Symbol presentation
    binaryDistinct : zeroSymbol ≡ oneSymbol → ⊥
    zeroNotBlank : zeroSymbol ≡ Presented.blank presentation → ⊥
    oneNotBlank : oneSymbol ≡ Presented.blank presentation → ⊥

    noneState : Presented.State presentation
    falseState : Presented.State presentation
    trueState : Presented.State presentation
    noneNotFalse : noneState ≡ falseState → ⊥
    noneNotTrue : noneState ≡ trueState → ⊥
    falseNotTrue : falseState ≡ trueState → ⊥

    querySteps : Nat → Nat
    queryCoefficient : Nat
    queryDegree : Nat

    finishConfiguration :
      Nat →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    execution :
      (index : Nat) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        (querySteps index)
        (Language.guardedStandardStart
          (Query.mapBoolSymbols
            zeroSymbol oneSymbol
            (Query.queryBits (Description.atIndex description index)))
          (querySteps index))
        (finishConfiguration index)

    finishStateExact :
      (index : Nat) →
      Standard.state (finishConfiguration index)
      ≡
      maybeOutputState noneState falseState trueState
        (Semantics.queryAnswer (Description.atIndex description index))

    queryStepsPolynomial :
      (index : Nat) →
      querySteps index
      ≤ queryPolynomialBudget
          queryCoefficient queryDegree description index

open FixedDescriptionCookBitGenerator public

------------------------------------------------------------------------
-- Semantic target may equivalently be stated with the proved streamed reader.
------------------------------------------------------------------------

finishStateExactStreaming :
  ∀ {description presentation}
    (generator : FixedDescriptionCookBitGenerator description presentation)
    (index : Nat) →
  Standard.state (finishConfiguration generator index)
  ≡
  maybeOutputState
    (noneState generator)
    (falseState generator)
    (trueState generator)
    (Streaming.streamedQueryBit (Description.atIndex description index))
finishStateExactStreaming {description} generator index
  rewrite Streaming.streamedQueryBitExact
    (Description.atIndex description index) =
  finishStateExact generator index

------------------------------------------------------------------------
-- ACTIVE CONSTRUCTION TARGET
--
-- Build this record for the fixed coded opposite target itself.  Because code,
-- rule table, state/symbol widths and local Cook windows are frozen, the
-- remaining complexity proof may treat those dimensions as program constants.
-- No polynomial claim uniform over arbitrary machine descriptions is required.
------------------------------------------------------------------------
