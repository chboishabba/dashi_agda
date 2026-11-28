module DASHI.Mathematics.Complexity.PNPVirtualEndpointWeldExact where

-- Connect the existing faithful virtual simulation directly to the existing
-- fixed-standard endpoint. No literal own-formula materialization required.
-- Actual generator, simulation, prefix, suffix and clock proof are inputs.
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clock
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as V
import DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualSimulationExact as Faithful
import DASHI.Mathematics.Complexity.PNPVirtualPaidEdgeBudgetNoGoExact as Paid
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Tools

module Close
  {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  {clocked : Clock.PolynomiallyClockedStandardCandidate candidate}
  (compiled : Faithful.FaithfulVirtualSelfQuotationCompilation clocked) where

  base = Faithful.base compiled
  fixed = V.fixedOfVirtualCompilation base
  standard = Clock.standard clocked
  code = Candidate.standardCandidateToCodeRealization standard
  target = Presented.finitePresentedStandardMachine (Fixed.presentation fixed)
  own = Fixed.fixedCookFormula fixed
  sim = V.candidateSimulation base
  mid = V.virtualRunTargetSteps sim

  closeVirtual :
    (prefix suffix : Nat) →
    (finish : Standard.StandardConfiguration target) →
    Run.StandardExactRun target prefix
      (Language.guardedStandardStart (Fixed.input fixed) (Fixed.steps fixed))
      (V.candidateTargetStart base) →
    Run.StandardExactRun target suffix (V.candidateTargetFinish base) finish →
    (prefix + mid + suffix) ≡ Fixed.steps fixed →
    Local.decideEqual
      (Presented.finiteState (Fixed.presentation fixed))
      (Standard.state finish)
      (Presented.acceptingState (Fixed.presentation fixed))
    ≡ Opposite.notBool
      (Local.decideEqual
        (Presented.finiteState (Candidate.presentation standard))
        (Standard.state (Candidate.finish standard own))
        (Presented.acceptingState (Candidate.presentation standard))) →
    Fixed.FixedStandardOppositeEndpointRealization code
  closeVirtual prefix suffix finish pre post fits negation = record
    { Fixed.fixed = fixed
    ; Fixed.finish = finish
    ; Fixed.execution = Tools.transportRunSteps fits
        (Tools.appendThreeExactRuns pre (V.virtualRunToTargetRun sim) post)
    ; Fixed.endpointDecisionExact = trans negation
        (cong Opposite.notBool (Candidate.decisionExact standard own))
    }

  endpointFailure : Fixed.FixedStandardOppositeEndpointRealization code →
    Direct.SATDecisionFailure candidate
  endpointFailure = Fixed.standardEndpointRealizationGivesDecisionFailure code

  -- The actual candidate run is already the middle source run of sim.
  -- If it consumes >= own-code bits, positive per-edge payment cannot fit.
  paidVirtualForcesZero :
    Paid.PaidEdges sim →
    Binary.formulaBitCodeLength own ≤ Candidate.exactSteps standard own →
    mid ≤ Fixed.steps fixed →
    Fixed.steps fixed ≡ zero
  paidVirtualForcesZero paid lengthPaid fits =
    Paid.lengthPaidClockForcesZero fixed
      (Candidate.exactSteps standard own) mid lengthPaid
      (Paid.paidSourceStepsBelowTarget sim paid) fits
