module DASHI.Mathematics.Complexity.PNotEqualsNPExtensionalCandidateAbstractMachineExact where

------------------------------------------------------------------------
-- EVERY EXTENSIONAL SAT CANDIDATE IS AN ABSTRACT ONE-STEP MACHINE
--
-- This owner isolates the exact representation seam in the self-reference
-- route.
--
-- PolynomialSATDeciderCandidate already contains:
--
--   decide : Cook.BooleanFormula -> Bool.
--
-- The generic DeterministicMachine carrier allows arbitrary configuration
-- types.  Therefore we can wrap ANY candidate as:
--
--   start phi  ->  done (decide phi)
--
-- in one transition.
--
-- Main result:
--
--   clockedDecision(candidateMachineExecution candidate) phi
--     = decide candidate phi.
--
-- So "machine realization" itself is not the missing theorem.
--
-- What this construction deliberately does NOT provide is a FINITE QUOTEABLE
-- program presentation: the transition function directly closes over the
-- extensional Agda function decide, and the configuration stores an arbitrary
-- Cook formula.  That finite-program realization is exactly what behavioral
-- self-reference still needs.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.DeterministicMachineToInPExact as ToP
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

------------------------------------------------------------------------
-- Two-stage configuration.
------------------------------------------------------------------------

data CandidateConfiguration : Set where
  start :
    Cook.BooleanFormula →
    CandidateConfiguration

  done :
    Bool →
    CandidateConfiguration

candidateMachine :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.PolynomialSATDeciderCandidate cost →
  Machine.DeterministicMachine
candidateMachine candidate = record
  { Machine.dInput =
      Cook.BooleanFormula
  ; Machine.dConfiguration =
      CandidateConfiguration
  ; Machine.dInitial =
      start
  ; Machine.dNext =
      next
  ; Machine.dAccepting =
      accepting
  }
  where
    next :
      CandidateConfiguration →
      Maybe CandidateConfiguration
    next (start formula) =
      just
        (done
          (Direct.decide candidate formula))
    next (done result) =
      nothing

    accepting :
      CandidateConfiguration →
      Set
    accepting (start formula) =
      Agda.Builtin.Equality._≡_ false true
    accepting (done result) =
      result ≡ true

------------------------------------------------------------------------
-- Exact one-step execution.
------------------------------------------------------------------------

candidateMachineExecution :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  ToP.ClockedDeterministicBooleanExecution
    (candidateMachine candidate)
candidateMachineExecution candidate = record
  { ToP.inputLength =
      Size.formulaNodeCount
  ; ToP.clock =
      λ inputSize → suc zero
  ; ToP.finalConfiguration =
      λ formula →
        done (Direct.decide candidate formula)
  ; ToP.runExact =
      λ formula → refl
  ; ToP.output =
      output
  }
  where
    output :
      CandidateConfiguration →
      Bool
    output (start formula) =
      false
    output (done result) =
      result

------------------------------------------------------------------------
-- The abstract machine is extensionally the original candidate.
------------------------------------------------------------------------

candidateMachineDecisionExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (formula : Cook.BooleanFormula) →
  ToP.clockedDecision
    (candidateMachineExecution candidate)
    formula
  ≡
  Direct.decide candidate formula
candidateMachineDecisionExact candidate formula =
  refl

candidateMachineRetainsPolynomialCertificate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  PR.polynomialTimeDecider
    cost
    (ToP.clockedDecision
      (candidateMachineExecution candidate))
candidateMachineRetainsPolynomialCertificate candidate =
  Direct.polynomialDecision candidate

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ExtensionalCandidateAbstractMachineBoundary : Set where
  constructor extensional-candidate-abstract-machine-boundary
  field
    everyCandidateHasAbstractOneStepMachine : Bool
    decisionPreservedDefinitionally : Bool
    polynomialCertificatePreserved : Bool
    finiteProgramSyntaxConstructed : Bool
    selfQuotationConstructed : Bool

canonicalExtensionalCandidateAbstractMachineBoundary :
  ExtensionalCandidateAbstractMachineBoundary
canonicalExtensionalCandidateAbstractMachineBoundary =
  extensional-candidate-abstract-machine-boundary
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Research consequence.
--
-- The remaining coverage seam is narrower than "turn D into a machine":
--
--   bare extensional D
--      -> abstract machine                      PAID
--      -> finite quoteable machine program      OPEN
--      -> binary/self-describing input adapter  OPEN
--      -> resource-aware behavioral fixed point OPEN.
------------------------------------------------------------------------
