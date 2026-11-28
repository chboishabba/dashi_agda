module DASHI.Mathematics.Complexity.PNPVirtualQuotientEndpointExact where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as RunTools
import DASHI.Mathematics.Complexity.RecursiveHyperfabricQuotientExact as Q
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as Virtual
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked

-- Existing master owner already turns the exact same-object opposite
-- endpoint into SAT failure. Do not make another Cook semantic premise.
module OnTarget {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  {code : Actual.CandidateCodeRealization candidate}
  (fixed : Fixed.FixedStandardOppositeMachine code) where

  presentation = Fixed.presentation fixed
  machine = Presented.finitePresentedStandardMachine presentation
  Config = Standard.StandardConfiguration machine
  start : Config
  start = Language.guardedStandardStart (Fixed.input fixed) (Fixed.steps fixed)
  observe : Config → Bool
  observe c = Local.decideEqual (Presented.finiteState presentation)
    (Standard.state c) (Presented.acceptingState presentation)

  -- A consumer-congruent chart may read the endpoint, not replace
  -- the literal same-target run with the length of the quotient path.
  fromExactRun : ∀ {K : Set} {g : K → Bool}
    (q : Q.QuotientStep Config K Bool observe g)
    (finish : Config) →
    Run.StandardExactRun machine (Fixed.steps fixed) start finish →
    g (Q.contract q finish) ≡ Opposite.notBool
      (Direct.decide candidate (Fixed.fixedCookFormula fixed)) →
    Fixed.FixedStandardOppositeEndpointRealization code
  fromExactRun q finish run flip = record
    { Fixed.fixed = fixed
    ; Fixed.finish = finish
    ; Fixed.execution = run
    ; Fixed.endpointDecisionExact = trans (sym (Q.closed q finish)) flip
    }

  failureFromExactRun : ∀ {K : Set} {g : K → Bool}
    (q : Q.QuotientStep Config K Bool observe g)
    (finish : Config) →
    Run.StandardExactRun machine (Fixed.steps fixed) start finish →
    g (Q.contract q finish) ≡ Opposite.notBool
      (Direct.decide candidate (Fixed.fixedCookFormula fixed)) →
    Direct.SATDecisionFailure candidate
  failureFromExactRun q finish run flip =
    Fixed.standardEndpointRealizationGivesDecisionFailure code
      (fromExactRun q finish run flip)

-- The construction must supply the original StandardExactRun and flip.
-- Existing VirtualQuotationFrontierExact.virtualRunToTargetRun supplies
-- the literal run for an inhabited virtual simulation; exact same-object
-- setup/resume/suffix and horizon equality remain producer obligations.

-- Attach directly to the existing virtual compiler, whose generator and
-- simulated candidate already live on the SAME coded fixed target.
module FromVirtual {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
  (compilation : Virtual.VirtualSelfQuotationCompilation clocked) where

  module T = OnTarget (Virtual.fixedOfVirtualCompilation compilation)
  sim = Virtual.candidateSimulation compilation
  simSteps = Virtual.virtualRunTargetSteps sim

  actualFailure : ∀ {K : Set} {g : K → Bool} {setup suffix : Nat}
    (q : Q.QuotientStep T.Config K Bool T.observe g)
    (finish : T.Config) →
    Run.StandardExactRun T.machine setup T.start
      (Virtual.candidateTargetStart compilation) →
    Run.StandardExactRun T.machine suffix
      (Virtual.candidateTargetFinish compilation) finish →
    ((setup + simSteps) + suffix) ≡
      Fixed.steps (Virtual.fixedOfVirtualCompilation compilation) →
    g (Q.contract q finish) ≡ Opposite.notBool
      (Direct.decide candidate
        (Fixed.fixedCookFormula (Virtual.fixedOfVirtualCompilation compilation))) →
    Direct.SATDecisionFailure candidate
  actualFailure q finish first last fits flip =
    T.failureFromExactRun q finish
      (RunTools.transportRunSteps fits
        (RunTools.appendThreeExactRuns first
          (Virtual.virtualRunToTargetRun sim) last)) flip

-- This receiver uses equality, not a bare <=; any padding needed to
-- inhabit the exact guarded horizon must be an actual suffix run.
