module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact where

------------------------------------------------------------------------
-- CONCRETE FINITE-CODE EXECUTION OF THE Q2 DESCENT
--
-- The finite self-specializing code calculus already pays:
--
--   * literal finite program syntax;
--   * executable specialization;
--   * executable diagonalization;
--   * definitional s-m-n and diagonal correctness.
--
-- This owner removes the remaining BoundedFixedPointExecutionRealization field
-- for the Q2 machine itself.
--
-- There is one primitive opcode: runBoundedDescent.  Its binary semantics
-- executes the already-total, well-founded Q2 step system and returns the
-- terminal state's current Cook formula.
--
-- Consequently the literal Kleene fixed point
--
--   specialize (diagonalize body) (diagonalize body)
--
-- evaluates definitionally to that terminal Cook formula.  The generic
-- BoundedFixedPointExecutionRealization record is therefore CONSTRUCTED rather
-- than assumed.
--
-- IMPORTANT: this does not prove the opposite-SAT semantics of the body.  That
-- remains the Q1/self-instantiation theorem.  What is paid here is precisely
-- EXEC-REALIZE: program code + interpreter + s-m-n + diagonal execution +
-- same-object fixed-point termination.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Maybe.Base using (nothing; just)
open import Data.Product using (proj₁)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedStateToPartialKleeneTerminationExact as Execute

------------------------------------------------------------------------
-- One literal primitive opcode.
------------------------------------------------------------------------

data Q2Primitive : Set where
  runBoundedDescent : Q2Primitive

------------------------------------------------------------------------
-- Canonical terminal state selected by the proved Q2 well-founded execution.
------------------------------------------------------------------------

canonicalTerminalState :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Q2.BoundedSelfReferenceState
canonicalTerminalState stepSystem initial =
  proj₁
    (Q2.boundedSelfReferenceHasTerminalState
      stepSystem
      initial)

canonicalTerminalFormula :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Cook.BooleanFormula
canonicalTerminalFormula stepSystem initial =
  Q2.currentFormula
    (canonicalTerminalState stepSystem initial)

------------------------------------------------------------------------
-- Concrete primitive semantics.
--
-- Unary execution is unused.  Binary execution returns the terminal Q2
-- formula.  The quoted program is still passed by the interpreter, so this is
-- a genuine instance of the same Program -> Program -> Input execution shape;
-- the current Q2 executor simply does not need to inspect that quote.
------------------------------------------------------------------------

q2PrimitiveSemantics :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Code.PrimitiveSemantics
    Q2Primitive
    ⊤
    Cook.BooleanFormula
q2PrimitiveSemantics stepSystem initial =
  record
    { Code.runPrimitive1 =
        λ primitive input →
          nothing
    ; Code.runPrimitive2 =
        λ primitive quoted input →
          just
            (canonicalTerminalFormula
              stepSystem
              initial)
    }

q2PartialSystem :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Kleene.PartialSpecializingProgramSystem
q2PartialSystem stepSystem initial =
  Code.finiteCodePartialSystem
    (q2PrimitiveSemantics stepSystem initial)

q2DiagonalCompiler :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Kleene.PartialDiagonalCompiler
    (q2PartialSystem stepSystem initial)
q2DiagonalCompiler stepSystem initial =
  Code.finiteCodeDiagonalCompiler
    (q2PrimitiveSemantics stepSystem initial)

q2BodyProgram :
  Code.Program Q2Primitive
q2BodyProgram =
  Code.primitive runBoundedDescent

------------------------------------------------------------------------
-- Literal fixed point and exact execution.
------------------------------------------------------------------------

q2FixedPointProgram :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Code.Program Q2Primitive
q2FixedPointProgram stepSystem initial =
  Kleene.partialFixedPointProgram
    (q2DiagonalCompiler stepSystem initial)
    q2BodyProgram

q2FixedPointIsLiteralFiniteCode :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  q2FixedPointProgram stepSystem initial
  ≡
  Code.primitiveBodyFixedPoint
    runBoundedDescent
q2FixedPointIsLiteralFiniteCode stepSystem initial =
  refl

q2FixedPointRunsToCanonicalTerminalFormula :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Kleene.run1
    (q2PartialSystem stepSystem initial)
    (q2FixedPointProgram stepSystem initial)
    tt
  ≡
  just
    (canonicalTerminalFormula
      stepSystem
      initial)
q2FixedPointRunsToCanonicalTerminalFormula
    stepSystem
    initial =
  refl

------------------------------------------------------------------------
-- EXEC-REALIZE is now an inhabitant, not an open field.
------------------------------------------------------------------------

q2FiniteCodeExecutionRealization :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Execute.BoundedFixedPointExecutionRealization
    stepSystem
    initial
    (q2PartialSystem stepSystem initial)
    (q2DiagonalCompiler stepSystem initial)
    q2BodyProgram
    tt
q2FiniteCodeExecutionRealization
    stepSystem
    initial =
  Execute.bounded-fixed-point-execution-realization
    terminalOutput
    terminalRun
  where
    terminalOutput :
      Q2.BoundedSelfReferenceState →
      Cook.BooleanFormula
    terminalOutput terminalState =
      canonicalTerminalFormula
        stepSystem
        initial

    terminalRun :
      (terminalState : Q2.BoundedSelfReferenceState) →
      Q2.next stepSystem terminalState ≡ nothing →
      Kleene.run1
        (q2PartialSystem stepSystem initial)
        (Kleene.partialFixedPointProgram
          (q2DiagonalCompiler stepSystem initial)
          q2BodyProgram)
        tt
      ≡
      just (terminalOutput terminalState)
    terminalRun terminalState terminalProof =
      q2FixedPointRunsToCanonicalTerminalFormula
        stepSystem
        initial

------------------------------------------------------------------------
-- Concrete termination witness.
------------------------------------------------------------------------

q2FiniteCodeFixedPointTerminates :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Kleene.TerminatesWith
    (q2FixedPointProgram stepSystem initial)
    tt
    (canonicalTerminalFormula stepSystem initial)
q2FiniteCodeFixedPointTerminates
    stepSystem
    initial =
  Kleene.terminates-with
    (q2FixedPointRunsToCanonicalTerminalFormula
      stepSystem
      initial)

------------------------------------------------------------------------
-- EXEC-REALIZE STATUS
--
-- Paid for the Q2 executor:
--
--   finite program code                PAID
--   partial interpreter                PAID
--   executable specialization / s-m-n  PAID
--   executable diagonal compiler       PAID
--   same-object fixed-point syntax     PAID
--   terminal Q2 -> actual run          PAID
--
-- Still NOT paid:
--
--   the primitive body must be shown to implement the special opposite-SAT
--   self-instantiation semantics.  That is no longer interpreter plumbing; it
--   is exactly the Q1 construction/semantic theorem.
------------------------------------------------------------------------
