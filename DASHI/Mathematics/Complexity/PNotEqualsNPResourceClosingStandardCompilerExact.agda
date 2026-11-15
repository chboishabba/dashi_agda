module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact where

------------------------------------------------------------------------
-- RESOURCE-CLOSING STANDARD COMPILER WITH EXPLICIT CANDIDATE SUBRUN
--
-- A bare endpoint equality can hide the hard theorem. This owner strengthens
-- the fixed-program compiler so the target machine must visibly contain:
--
--   prefix/setup
--      ; edge-for-edge simulation of D on the target's OWN Cook formula
--      ; finite negation suffix.
--
-- The candidate middle run is the exact run already stored in the conventional
-- finite standard candidate witness. A StandardMachineSimulation maps every
-- one of its edges into the target fixed machine. Total time is the literal
-- sum prefix + candidate + suffix, transported to the Cook budget T.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as StandardOpposite
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedProgramStandardCompilerExact as Compiler
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as StandardRun
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

------------------------------------------------------------------------
-- Strong compilation receipt for one polynomially-clocked candidate.
------------------------------------------------------------------------

record ResourceClosingFixedProgramCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : Clocked.PolynomiallyClockedStandardCandidate candidate) : Set₃ where
  field
    fixed :
      StandardOpposite.FixedStandardOppositeMachine
        (Candidate.standardCandidateToCodeRealization
          (Clocked.standard clocked))

    simulation :
      Simulation.StandardMachineSimulation
        (Presented.finitePresentedStandardMachine
          (Candidate.presentation (Clocked.standard clocked)))
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))

    prefixSteps : Nat
    suffixSteps : Nat

    finish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))

    prefix :
      StandardRun.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))
        prefixSteps
        (Language.guardedStandardStart
          (StandardOpposite.input fixed)
          (StandardOpposite.steps fixed))
        (Simulation.embed simulation
          (Language.guardedStandardStart
            (Candidate.encodeFormula
              (Clocked.standard clocked)
              (StandardOpposite.fixedCookFormula fixed))
            (Candidate.exactSteps
              (Clocked.standard clocked)
              (StandardOpposite.fixedCookFormula fixed))))

    suffix :
      StandardRun.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))
        suffixSteps
        (Simulation.embed simulation
          (Candidate.finish
            (Clocked.standard clocked)
            (StandardOpposite.fixedCookFormula fixed)))
        finish

    totalStepsExact :
      (prefixSteps
        + Candidate.exactSteps
            (Clocked.standard clocked)
            (StandardOpposite.fixedCookFormula fixed)
        + suffixSteps)
      ≡ StandardOpposite.steps fixed

    -- The suffix performs only the final Boolean polarity change. It is stated
    -- against the literal finite-control observations of source and target.
    negationExact :
      Local.decideEqual
        (Presented.finiteState (StandardOpposite.presentation fixed))
        (Standard.state finish)
        (Presented.acceptingState (StandardOpposite.presentation fixed))
      ≡
      Opposite.notBool
        (Local.decideEqual
          (Presented.finiteState
            (Candidate.presentation (Clocked.standard clocked)))
          (Standard.state
            (Candidate.finish
              (Clocked.standard clocked)
              (StandardOpposite.fixedCookFormula fixed)))
          (Presented.acceptingState
            (Candidate.presentation (Clocked.standard clocked))))

open ResourceClosingFixedProgramCompilation public

------------------------------------------------------------------------
-- The middle phase is literally the candidate's own run, mapped edge-for-edge.
------------------------------------------------------------------------

candidateOwnFormulaRun :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : ResourceClosingFixedProgramCompilation clocked) →
  StandardRun.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (StandardOpposite.presentation (fixed resource)))
    (Candidate.exactSteps
      (Clocked.standard clocked)
      (StandardOpposite.fixedCookFormula (fixed resource)))
    (Simulation.embed (simulation resource)
      (Language.guardedStandardStart
        (Candidate.encodeFormula
          (Clocked.standard clocked)
          (StandardOpposite.fixedCookFormula (fixed resource)))
        (Candidate.exactSteps
          (Clocked.standard clocked)
          (StandardOpposite.fixedCookFormula (fixed resource)))))
    (Simulation.embed (simulation resource)
      (Candidate.finish
        (Clocked.standard clocked)
        (StandardOpposite.fixedCookFormula (fixed resource))))
candidateOwnFormulaRun {clocked = clocked} resource =
  Simulation.simulateExactRun
    (simulation resource)
    (Candidate.execution
      (Clocked.standard clocked)
      (StandardOpposite.fixedCookFormula (fixed resource)))

------------------------------------------------------------------------
-- Candidate polynomiality is preserved visibly inside the middle phase.
------------------------------------------------------------------------

candidateOwnFormulaPolynomialBound :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : ResourceClosingFixedProgramCompilation clocked) →
  Candidate.exactSteps
      (Clocked.standard clocked)
      (StandardOpposite.fixedCookFormula (fixed resource))
  ≤
  Clocked.polynomialStepBudget
    (Clocked.clockCoefficient clocked)
    (Clocked.clockDegree clocked)
    (StandardOpposite.fixedCookFormula (fixed resource))
candidateOwnFormulaPolynomialBound {clocked = clocked} resource =
  Clocked.exactStepsPolynomialBound
    clocked
    (StandardOpposite.fixedCookFormula (fixed resource))

------------------------------------------------------------------------
-- Compose the three target-machine phases and transport to the exact Cook T.
------------------------------------------------------------------------

resourceClosingExecution :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (resource : ResourceClosingFixedProgramCompilation clocked) →
  StandardRun.StandardExactRun
    (Presented.finitePresentedStandardMachine
      (StandardOpposite.presentation (fixed resource)))
    (StandardOpposite.steps (fixed resource))
    (Language.guardedStandardStart
      (StandardOpposite.input (fixed resource))
      (StandardOpposite.steps (fixed resource)))
    (finish resource)
resourceClosingExecution resource =
  Simulation.transportRunSteps
    (totalStepsExact resource)
    (Simulation.appendThreeExactRuns
      (prefix resource)
      (candidateOwnFormulaRun resource)
      (suffix resource))

------------------------------------------------------------------------
-- Strong resource receipt -> the weaker fixed-program compiler automatically.
------------------------------------------------------------------------

resourceClosingToFixedProgramCompilation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate} →
  ResourceClosingFixedProgramCompilation clocked →
  Compiler.FixedProgramStandardCompilation
    (Candidate.standardCandidateToCodeRealization
      (Clocked.standard clocked))
resourceClosingToFixedProgramCompilation
    {candidate = candidate}
    {clocked = clocked}
    resource = record
  { Compiler.fixed = fixed resource
  ; Compiler.finish = finish resource
  ; Compiler.execution = resourceClosingExecution resource
  ; Compiler.executionSemanticsExact = semanticsExact
  }
  where
    ownFormula : Cook.BooleanFormula
    ownFormula = StandardOpposite.fixedCookFormula (fixed resource)

    sourceDecisionExact :
      Local.decideEqual
        (Presented.finiteState
          (Candidate.presentation (Clocked.standard clocked)))
        (Standard.state
          (Candidate.finish (Clocked.standard clocked) ownFormula))
        (Presented.acceptingState
          (Candidate.presentation (Clocked.standard clocked)))
      ≡ Direct.decide candidate ownFormula
    sourceDecisionExact =
      Candidate.decisionExact (Clocked.standard clocked) ownFormula

    finalOpposite :
      Local.decideEqual
        (Presented.finiteState (StandardOpposite.presentation (fixed resource)))
        (Standard.state (finish resource))
        (Presented.acceptingState (StandardOpposite.presentation (fixed resource)))
      ≡ Opposite.notBool (Direct.decide candidate ownFormula)
    finalOpposite =
      trans
        (negationExact resource)
        (cong Opposite.notBool sourceDecisionExact)

    semanticsExact :
      just
        (Local.decideEqual
          (Presented.finiteState
            (StandardOpposite.presentation (fixed resource)))
          (Standard.state (finish resource))
          (Presented.acceptingState
            (StandardOpposite.presentation (fixed resource))))
      ≡
      Fixed.fixedRun
        (Candidate.standardCandidateToCodeRealization
          (Clocked.standard clocked))
        ownFormula
    semanticsExact =
      trans
        (cong just finalOpposite)
        (sym
          (Fixed.fixedRunExact
            (Candidate.standardCandidateToCodeRealization
              (Clocked.standard clocked))
            ownFormula))

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The hard compiler theorem can no longer hide an oracle-like endpoint field.
-- It must expose:
--   * a real standard-machine simulation of the candidate program;
--   * the candidate's exact run on the fixed machine's own Cook formula;
--   * its inherited polynomial clock bound;
--   * explicit prefix/suffix phases;
--   * exact additive total-time closure;
--   * a finite-control negation law.
--
-- The remaining genuinely self-referential part is now concentrated in the
-- prefix/setup phase: construct the fixed finite program and arrange its own
-- Cook formula as the literal candidate input while closing the total T budget.
------------------------------------------------------------------------
