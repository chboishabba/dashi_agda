module DASHI.Mathematics.Complexity.PNotEqualsNPFixedDescriptionVirtualGeneratorExact where

------------------------------------------------------------------------
-- ACTIVE GENERATOR CONTRACT FOR ONE IMMUTABLE SELF-QUOTATION DESCRIPTION
--
-- The stronger `UniversalGuardedCookBitGenerator` quantifies over arbitrary
-- coded machines.  The current one-hot/truth-table Cook implementation does not
-- justify a uniform polynomial clock in that varying-machine code.
--
-- Self-quotation needs only one fixed description D = (machine,input,T), while
-- requested index i varies.  This owner states exactly that contract.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.GuardedCookFixedDescriptionStreamingCostExact as Cost
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

record FixedDescriptionGuardedCookBitGenerator
    (description : Description.GuardedCookFormulaDescription)
    (presentation : Presented.FinitePresentedStandardTM) : Set₂ where
  field
    zeroSymbol : Presented.Symbol presentation
    oneSymbol : Presented.Symbol presentation
    binaryDistinct : zeroSymbol ≡ oneSymbol → ⊥
    zeroNotBlank : zeroSymbol ≡ Presented.blank presentation → ⊥
    oneNotBlank : oneSymbol ≡ Presented.blank presentation → ⊥

    querySteps : Nat → Nat

    finishConfiguration :
      (index : Nat) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    execution :
      (index : Nat) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        (querySteps index)
        (Language.guardedStandardStart
          {machine = Presented.finitePresentedStandardToConcrete presentation}
          (Query.mapBoolSymbols
            zeroSymbol oneSymbol
            (Query.queryBits (Description.atIndex description index)))
          (querySteps index))
        (finishConfiguration index)

    outputBit :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation) →
      Maybe Bool

    outputExact :
      (index : Nat) →
      outputBit (finishConfiguration index)
      ≡ Semantics.queryAnswer (Description.atIndex description index)

    queryStepsLinear :
      (index : Nat) →
      querySteps index
      ≤ Cost.fixedDescriptionLinearBudget
          description
          (Query.queryBitLength (Description.atIndex description index))

open FixedDescriptionGuardedCookBitGenerator public

------------------------------------------------------------------------
-- Successful in-range reads are therefore exactly the canonical Cook bit.
------------------------------------------------------------------------

fixedGeneratorSuccessfulBitExact :
  ∀ {description presentation}
    (generator : FixedDescriptionGuardedCookBitGenerator description presentation)
    (index : Nat)
    (bit : Bool) →
  Semantics.queryAnswer (Description.atIndex description index) ≡ just bit →
  outputBit generator (finishConfiguration generator index) ≡ just bit
fixedGeneratorSuccessfulBitExact generator index bit semantic =
  trans
    (outputExact generator index)
    semantic

------------------------------------------------------------------------
-- TRUST BOUNDARY
--
-- This is still an interface, not an inhabitant.  What has now been paid below
-- it is the exact streamed semantic evaluator and a fixed-description linear
-- semantic-work envelope.  Remaining implementation is a compiler from that
-- evaluator into a finite coded standard machine with an exact run/clock that
-- inhabits this record.
------------------------------------------------------------------------
