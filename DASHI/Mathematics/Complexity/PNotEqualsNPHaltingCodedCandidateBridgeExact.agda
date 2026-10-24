module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateBridgeExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED DECIDER -> EXISTING STANDARD CANDIDATE/CLOCK STACK
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as InputCodec
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.CodedStandardGuardedExecutionCompilerExact as GuardedCompiler
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked

haltingWitnessToStandardCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Halting.GuardedExecutionReceipt witness →
  Candidate.StandardFiniteCandidateCode candidate
haltingWitnessToStandardCandidate witness guarded = record
  { Candidate.presentation =
      Coded.decodeCodedStandardTM (Halting.code witness)
  ; Candidate.stateCoverage =
      Coded.codedStateCoverage (Halting.code witness)
  ; Candidate.symbolCoverage =
      Coded.codedSymbolCoverage (Halting.code witness)
  ; Candidate.encodeFormula =
      InputCodec.formulaInput
        (Halting.code witness)
        (Halting.zeroSymbol witness)
        (Halting.oneSymbol witness)
  ; Candidate.exactSteps = Halting.actualSteps witness
  ; Candidate.finish = Halting.guardedFinish guarded
  ; Candidate.execution = Halting.guardedExecution guarded
  ; Candidate.decisionExact = Halting.guardedDecisionExact guarded
  }

haltingWitnessToPolynomiallyClockedCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  (guarded : Halting.GuardedExecutionReceipt witness) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
haltingWitnessToPolynomiallyClockedCandidate witness guarded = record
  { Clocked.standard = haltingWitnessToStandardCandidate witness guarded
  ; Clocked.clockCoefficient = Halting.clockCoefficient witness
  ; Clocked.clockDegree = Halting.clockDegree witness
  ; Clocked.exactStepsPolynomialBound =
      Halting.actualStepsPolynomialBound witness
  }

------------------------------------------------------------------------
-- Guarded representation is now compiler-owned, so the normal constructors no
-- longer need it as a user-supplied premise.
------------------------------------------------------------------------

automaticGuardedExecutionReceipt :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Halting.GuardedExecutionReceipt witness
automaticGuardedExecutionReceipt =
  GuardedCompiler.guardedExecutionReceiptOfHaltingWitness

haltingWitnessToStandardCandidateAutomatic :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Candidate.StandardFiniteCandidateCode candidate
haltingWitnessToStandardCandidateAutomatic witness =
  haltingWitnessToStandardCandidate
    witness
    (automaticGuardedExecutionReceipt witness)

haltingWitnessToPolynomiallyClockedCandidateAutomatic :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
haltingWitnessToPolynomiallyClockedCandidateAutomatic witness =
  haltingWitnessToPolynomiallyClockedCandidate
    witness
    (automaticGuardedExecutionReceipt witness)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Every theorem downstream of `PolynomiallyClockedStandardCandidate` can now be
-- reused from one actual-halting coded witness alone.  The Cook guard padding is
-- a representation compiler and no longer a separate proof/mathematics input.
------------------------------------------------------------------------
