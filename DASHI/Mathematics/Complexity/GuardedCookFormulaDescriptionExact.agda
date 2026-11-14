module DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact where

------------------------------------------------------------------------
-- INDEX-FREE DESCRIPTION OF ONE GUARDED COOK FORMULA
--
-- The universal virtual source must keep machine/input/T fixed while indices
-- vary.  This owner makes that separation structural rather than conventional.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query

record GuardedCookFormulaDescription : Set₁ where
  field
    code : Coded.CodedFiniteStandardTM

    nonemptyRules :
      Selector.NonemptyRuleTable
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM code))

    input :
      Input.InputWord
        (Presented.finitePresentedStandardToConcrete
          (Coded.decodeCodedStandardTM code))

    steps : Nat

open GuardedCookFormulaDescription public

formula : GuardedCookFormulaDescription → Cook.BooleanFormula
formula description =
  CookLevin.guardedCookFormula
    (Coded.codedStateCoverage (code description))
    (Coded.codedSymbolCoverage (code description))
    (nonemptyRules description)
    (input description)
    (steps description)

atIndex :
  GuardedCookFormulaDescription → Nat → Query.GuardedCookBitQuery
atIndex description requested = record
  { Query.code = code description
  ; Query.nonemptyRules = nonemptyRules description
  ; Query.input = input description
  ; Query.steps = steps description
  ; Query.index = requested
  }

atIndexFormulaExact :
  (description : GuardedCookFormulaDescription)
  (requested : Nat) →
  Query.queryFormula (atIndex description requested)
  ≡ formula description
atIndexFormulaExact description requested = refl

atIndexOnlyChangesIndex :
  (description : GuardedCookFormulaDescription)
  (left right : Nat) →
  Query.withIndex (atIndex description left) right
  ≡ atIndex description right
atIndexOnlyChangesIndex description left right = refl

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- A virtual Cook source is now indexed by one immutable description.  No
-- machine code, input word, rule witness, or Cook budget may vary with a read;
-- only the requested index is an argument to `atIndex`.
------------------------------------------------------------------------
