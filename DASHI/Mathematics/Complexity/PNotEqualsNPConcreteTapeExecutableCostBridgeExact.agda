module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableCostBridgeExact where

------------------------------------------------------------------------
-- DETERMINISTIC CONCRETE TAPE CODE -> EXECUTABLE COST REFINEMENT
------------------------------------------------------------------------

open import Data.Product using (_,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as Executable
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as ProgramCode
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Same literal tape bit-vector as the generic executable-code carrier.
------------------------------------------------------------------------

tapeCandidateExecutableDeciderCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Tape.CandidateDeterministicTapeCode candidate →
  Executable.ExecutableDeciderCode (Direct.decide candidate)
tapeCandidateExecutableDeciderCode tape = record
  { Executable.Code =
      CNF.Bits
        (ProgramCode.StaticProgramBitsWidth
          (Tape.machine tape))
  ; Executable.code =
      Tape.candidateProgramBits tape
  ; Executable.run =
      λ codeBits formula →
        Tape.endpointDecision
          (Tape.finalInterior tape formula)
  ; Executable.runExact =
      Tape.decisionExact tape
  ; Executable.codeSize =
      λ codeBits →
        Tape.candidateProgramBitSize tape
  }

------------------------------------------------------------------------
-- Therefore every deterministic tape candidate is an executable polynomial
-- decider witness over the SAME base polynomial certificate.
------------------------------------------------------------------------

tapeCandidateExecutablePolynomialWitness :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  Executable.ExecutablePolynomialTimeDecider
    cost
    (Direct.decide candidate)
tapeCandidateExecutablePolynomialWitness
    {candidate = candidate}
    tape =
  Direct.polynomialDecision candidate
  ,
  tapeCandidateExecutableDeciderCode tape

liftTapeCandidateToExecutableCost :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    (closure : Executable.ExecutableCodeClosure Cook.BooleanFormula)
    {candidate : Direct.PolynomialSATDeciderCandidate base}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  Direct.PolynomialSATDeciderCandidate
    (Executable.executablePolynomialCostModel base closure)
liftTapeCandidateToExecutableCost
    closure
    {candidate = candidate}
    tape =
  Direct.polynomial-sat-decider-candidate
    (Direct.decide candidate)
    (tapeCandidateExecutablePolynomialWitness tape)

------------------------------------------------------------------------
-- Converse lowering remains a separate same-model obligation.
------------------------------------------------------------------------

record ConcreteTapeCodeLowering
    {base : PR.PolynomialCostModel Cook.BooleanFormula}
    (closure : Executable.ExecutableCodeClosure Cook.BooleanFormula) : Set₂ where
  field
    lower :
      (candidate :
        Direct.PolynomialSATDeciderCandidate
          (Executable.executablePolynomialCostModel base closure)) →
      Tape.CandidateDeterministicTapeCode candidate

open ConcreteTapeCodeLowering public

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Paid:
--   concrete deterministic tape code -> executable finite code refinement.
--
-- Not paid:
--   arbitrary executable finite code -> concrete deterministic tape program.
--
-- A `ConcreteTapeCodeLowering` is exactly the missing standard-model compiler
-- before universal executable-cost quantification enters concrete Cook--Levin.
------------------------------------------------------------------------
