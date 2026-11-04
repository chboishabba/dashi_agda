module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingQuotationScaleExact where

------------------------------------------------------------------------
-- RESOURCE CLOSURE x ACTUAL COOK-QUOTATION GROWTH
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)
open import Data.Nat.Base using (_≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact as Budget
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinQuotationGrowthExact as Growth
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

nonemptySeedStrictlyBelowOwnCookBitCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked)
    (symbol : Local.Symbol
      (Opposite.fixedConcreteMachine (Resource.fixed resource)))
    (rest : List
      (Local.Symbol
        (Opposite.fixedConcreteMachine (Resource.fixed resource)))) →
  Opposite.input (Resource.fixed resource) ≡ symbol ∷ rest →
  Input.inputPayloadLength (Opposite.input (Resource.fixed resource))
  <
  Binary.formulaBitCodeLength
    (Opposite.fixedCookFormula (Resource.fixed resource))
nonemptySeedStrictlyBelowOwnCookBitCode
    resource symbol rest inputExact
    rewrite inputExact =
  Growth.nonemptyPayloadStrictlyBelowCookFormulaBitCode
    (Opposite.stateCoverage (Resource.fixed resource))
    (Opposite.symbolCoverage (Resource.fixed resource))
    (Opposite.nonemptyRules (Resource.fixed resource))
    symbol rest
    (Opposite.steps (Resource.fixed resource))

exactDisplayedPolynomialBudgetFitsCookBudget :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked) →
  Budget.candidateOwnSteps resource
  ≡
  Clocked.polynomialStepBudget
    (Clocked.clockCoefficient clocked)
    (Clocked.clockDegree clocked)
    (Opposite.fixedCookFormula (Resource.fixed resource)) →
  Clocked.polynomialStepBudget
    (Clocked.clockCoefficient clocked)
    (Clocked.clockDegree clocked)
    (Opposite.fixedCookFormula (Resource.fixed resource))
  ≤ Opposite.steps (Resource.fixed resource)
exactDisplayedPolynomialBudgetFitsCookBudget resource exactClock =
  subst
    (λ steps → steps ≤ Opposite.steps (Resource.fixed resource))
    exactClock
    (Budget.candidateOwnStepsFitCookBudget resource)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- A successful prefix must genuinely expand a finite seed into a larger own
-- Cook quotation while leaving the candidate run inside the same exact T.
-- These are necessary conditions only; neither theorem constructs the prefix.
------------------------------------------------------------------------
