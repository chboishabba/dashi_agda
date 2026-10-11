module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeExecutableCostBridgeExact where

------------------------------------------------------------------------
-- DETERMINISTIC CONCRETE TAPE CODE -> EXECUTABLE COST REFINEMENT
--
-- Reuse:
--   PNotEqualsNPExecutablePolynomialCostRefinementExact
--   PNotEqualsNPCandidateDeterministicTapeCodeExact
--
-- The executable-cost owner already distinguishes:
--
--   abstract polynomial witness
--       vs
--   polynomial witness + finite executable code.
--
-- The deterministic-tape owner now supplies a stronger code object:
--   literal ConcreteTapeProgramDescription
--   + deterministic execution
--   + exact candidate decision at the final control state.
--
-- This owner proves the FORGETFUL/embedding direction exactly.  It does NOT
-- claim that an arbitrary ExecutableDeciderCode can be lowered to the concrete
-- tape model.  That converse is the concrete interpreter/compiler frontier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as Executable
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as ProgramCode

------------------------------------------------------------------------
-- Same literal tape program as the generic executable-code carrier.
------------------------------------------------------------------------

tapeCandidateExecutableDeciderCode :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Tape.CandidateDeterministicTapeCode candidate →
  Executable.ExecutableDeciderCode (Direct.decide candidate)
tapeCandidateExecutableDeciderCode tape = record
  { Executable.Code =
      ProgramCode.ConcreteTapeProgramDescription
        (Tape.machine tape)
  ; Executable.code =
      Tape.candidateProgramDescription tape
  ; Executable.run =
      λ description formula →
        Tape.endpointDecision
          (Tape.finalInterior tape formula)
  ; Executable.runExact =
      Tape.decisionExact tape
  ; Executable.codeSize =
      λ description →
        Tape.candidateProgramBitSize tape
  }

------------------------------------------------------------------------
-- Therefore every deterministic tape candidate is an executable polynomial
-- decider witness over the SAME base polynomial certificate.
------------------------------------------------------------------------

tapeCandidateExecutablePolynomialWitness :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Tape.CandidateDeterministicTapeCode candidate →
  Executable.ExecutablePolynomialTimeDecider
    cost
    (Direct.decide candidate)
tapeCandidateExecutablePolynomialWitness tape =
  Direct.polynomialDecision _
  ,
  tapeCandidateExecutableDeciderCode tape

------------------------------------------------------------------------
-- Lift one base-model candidate to the existing executable refined cost model.
------------------------------------------------------------------------

liftTapeCandidateToExecutableCost :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    (closure : Executable.ExecutableCodeClosure Cook.BooleanFormula)
    {candidate : Direct.PolynomialSATDeciderCandidate base} →
  Tape.CandidateDeterministicTapeCode candidate →
  Direct.PolynomialSATDeciderCandidate
    (Executable.executablePolynomialCostModel base closure)
liftTapeCandidateToExecutableCost closure tape =
  Direct.polynomial-sat-decider-candidate
    (Direct.decide _)
    (tapeCandidateExecutablePolynomialWitness tape)

------------------------------------------------------------------------
-- The generic executable code recovered from the refined witness is literally
-- the tape-backed code supplied above up to the fields used by the realization
-- lane.  No new decision semantics is introduced here.
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
-- A `ConcreteTapeCodeLowering` is therefore exactly the missing standard-model
-- compiler needed before universal quantification over the executable cost
-- refinement can enter the concrete Cook--Levin / opposite-interpreter lane.
------------------------------------------------------------------------
