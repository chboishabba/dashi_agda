module DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixConcreteWriteExact where

------------------------------------------------------------------------
-- THE ACTUAL RESOURCE-CLOSING PREFIX REIFIES TO <= p LITERAL SYMBOL WRITES
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact as Budget

import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeHeadMarginExact as Margin
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact as Reverse
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes

weakenHeadMarginTo :
  ∀ {State Symbol : Set}
    {small large : Nat}
    {cells : List (Local.TapeCell State Symbol)} →
  small ≤ large →
  Margin.HeadMargin large cells →
  Margin.HeadMargin small cells
weakenHeadMarginTo small≤large margin = record
  { Margin.leftMargin =
      NatP.≤-trans small≤large (Margin.leftMargin margin)
  ; Margin.rightMargin =
      NatP.≤-trans small≤large (Margin.rightMargin margin)
  }

record ReifiedStructuralPrefix
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) : Set₃ where
  field
    reified :
      Reverse.ReifiedStandardRun
        (Guard.guardedInitialRow
          (Opposite.input (Resource.fixed base))
          (Opposite.steps (Resource.fixed base)))
        (Language.guardedInitialUnique
          (Opposite.input (Resource.fixed base))
          (Opposite.steps (Resource.fixed base)))
        (Resource.prefix base)
  where
    base = StructuralResource.resource structuralResource

open ReifiedStructuralPrefix public

reifyStructuralPrefix :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  ReifiedStructuralPrefix structuralResource
reifyStructuralPrefix structuralResource = record
  { reified =
      Reverse.reifyStandardRun
        (Presented.finitePresentedStandardToConcrete_dispatchUnique
          (Opposite.presentation (Resource.fixed base)))
        startUnique
        refl
        prefixMargin
        (Resource.prefix base)
  }
  where
    base = StructuralResource.resource structuralResource

    fixedInput = Opposite.input (Resource.fixed base)
    totalSteps = Opposite.steps (Resource.fixed base)
    prefixSteps = Resource.prefixSteps base

    startUnique =
      Language.guardedInitialUnique fixedInput totalSteps

    prefixBelowTotal : prefixSteps ≤ totalSteps
    prefixBelowTotal = Budget.prefixFitsCookBudget base

    prefixMargin :
      Margin.HeadMargin (suc prefixSteps)
        (Local.cells (Guard.guardedInitialRow fixedInput totalSteps))
    prefixMargin =
      weakenHeadMarginTo
        (s≤s prefixBelowTotal)
        (Guard.guardedInitialMargin fixedInput totalSteps)

prefixConcreteRunLengthExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Run.runLength
    (Reverse.concreteRun
      (reified (reifyStructuralPrefix structuralResource)))
  ≡ Resource.prefixSteps
      (StructuralResource.resource structuralResource)
prefixConcreteRunLengthExact structuralResource =
  Language.reifiedRunLengthExact
    (Presented.finitePresentedStandardToConcrete_dispatchUnique
      (Opposite.presentation (Resource.fixed base)))
    startUnique
    refl
    prefixMargin
    (Resource.prefix base)
  where
    base = StructuralResource.resource structuralResource
    fixedInput = Opposite.input (Resource.fixed base)
    totalSteps = Opposite.steps (Resource.fixed base)
    prefixSteps = Resource.prefixSteps base
    startUnique = Language.guardedInitialUnique fixedInput totalSteps
    prefixMargin =
      weakenHeadMarginTo
        (s≤s (Budget.prefixFitsCookBudget base))
        (Guard.guardedInitialMargin fixedInput totalSteps)

prefixConcreteWritesWithin :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Writes.SymbolWritesWithin
    (Resource.prefixSteps
      (StructuralResource.resource structuralResource))
    (Writes.eraseRow
      (Guard.guardedInitialRow
        (Opposite.input
          (Resource.fixed
            (StructuralResource.resource structuralResource)))
        (Opposite.steps
          (Resource.fixed
            (StructuralResource.resource structuralResource)))))
    (Writes.eraseRow
      (Reverse.finish
        (reified (reifyStructuralPrefix structuralResource))))
prefixConcreteWritesWithin structuralResource
    rewrite sym (prefixConcreteRunLengthExact structuralResource) =
  Writes.wellFormedRunErasesToWritesWithin
    (Reverse.concreteRun
      (reified (reifyStructuralPrefix structuralResource)))

------------------------------------------------------------------------
-- RESOURCE CONSEQUENCE
--
-- The exact prefix used by the structural resource-closing compiler is now
-- charged in the literal tape-write currency:
--
--   prefixSteps = p  =>  at most p same-position symbol rewrites.
--
-- The remaining content theorem must connect the reified prefix endpoint to
-- the structurally embedded own-formula candidate input and lower-bound how
-- many of those writes are necessarily nontrivial.
------------------------------------------------------------------------
