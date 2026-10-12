module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingQuotationScaleExact where

------------------------------------------------------------------------
-- RESOURCE CLOSURE x ACTUAL COOK-QUOTATION GROWTH
--
-- Two independently proved facts meet here:
--
--   1. a resource-closing compiler forces candidateSteps(ownCL) <= T;
--   2. the actual full-tableau Cook constructor has
--        nonempty seed payload < bitCodeLength(ownCL).
--
-- Thus a successful prefix cannot be literal source-string self-input.  It must
-- expand a smaller finite seed into the larger behavioural Cook quotation while
-- still leaving enough of the SAME T budget to execute the candidate and suffix.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingBudgetNecessityExact as Budget
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinQuotationGrowthExact as Growth
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

------------------------------------------------------------------------
-- Nonempty fixed seed is strictly shorter than its own Cook quotation.
------------------------------------------------------------------------

nonemptySeedStrictlyBelowOwnCookBitCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : Resource.ResourceClosingFixedProgramCompilation clocked)
    (symbol :
      DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact.Symbol
        (Opposite.fixedConcreteMachine (Resource.fixed resource)))
    (rest :
      List
        (DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact.Symbol
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
    symbol
    rest
    (Opposite.steps (Resource.fixed resource))

------------------------------------------------------------------------
-- If a clocked candidate's exact own-formula run equals its displayed
-- polynomial budget, that whole polynomial budget must fit inside T.
------------------------------------------------------------------------

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
-- The remaining prefix theorem must simultaneously pay:
--
--   finite seed --(actual execution)--> larger own Cook quotation
--   candidateClock(own Cook quotation) <= same Cook budget T.
--
-- Existing growth gives the first strict size direction; resource decomposition
-- gives the second budget direction.  Neither theorem reverses these arrows or
-- asserts the missing prefix exists.
------------------------------------------------------------------------
