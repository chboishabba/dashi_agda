module DASHI.Mathematics.Complexity.PNotEqualsNPBoundedStateToPartialKleeneTerminationExact where

------------------------------------------------------------------------
-- Q2 TERMINATION -> ACTUAL PARTIAL-KLEENE FIXED-POINT TERMINATION
--
-- PNotEqualsNPBoundedSelfReferenceWellFoundedExact proves that a TOTAL
-- Maybe-valued recursive state transition with strict whole-state descent has a
-- terminal state.
--
-- That alone must NOT be confused with termination of the actual partial
-- Kleene fixed-point program.
--
-- This owner types the missing execution-realization seam explicitly.  A
-- realization must prove that every terminal Q2 state corresponds to a concrete
-- terminating output of the partial fixed-point program.  Once that proof is
-- supplied, Nat well-foundedness produces an actual Kleene.TerminatesWith
-- witness.
--
-- The final theorem composes this with the existing exact-SAT divergence
-- theorem: under SAT in P and an opposite-SAT body, such a realized bounded
-- step system is contradictory.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe.Base using (nothing; just)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneToSelfDiagonalExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact as NoGo

------------------------------------------------------------------------
-- Realization of abstract Q2 terminal states by the actual fixed-point run.
------------------------------------------------------------------------

record BoundedFixedPointExecutionRealization
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState)
    (system : Kleene.PartialSpecializingProgramSystem)
    (compiler : Kleene.PartialDiagonalCompiler system)
    (bodyProgram : Kleene.Program system)
    (dynamicInput : Kleene.Input system) : Set₁ where
  constructor bounded-fixed-point-execution-realization
  field
    terminalOutput :
      Q2.BoundedSelfReferenceState →
      Kleene.Output system

    terminalRealizesFixedPointRun :
      (terminalState : Q2.BoundedSelfReferenceState) →
      Q2.next stepSystem terminalState ≡ nothing →
      Kleene.run1
        system
        (Kleene.partialFixedPointProgram
          compiler
          bodyProgram)
        dynamicInput
      ≡
      just (terminalOutput terminalState)

open BoundedFixedPointExecutionRealization public

------------------------------------------------------------------------
-- Generic compiler: Q2 well-foundedness -> actual Kleene termination.
------------------------------------------------------------------------

boundedStateTerminationGivesPartialFixedPointTermination :
  ∀ {system : Kleene.PartialSpecializingProgramSystem}
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState)
    (compiler : Kleene.PartialDiagonalCompiler system)
    (bodyProgram : Kleene.Program system)
    (dynamicInput : Kleene.Input system)
    (realization :
      BoundedFixedPointExecutionRealization
        stepSystem
        initial
        system
        compiler
        bodyProgram
        dynamicInput) →
  Σ (Kleene.Output system)
    (λ output →
      Kleene.TerminatesWith
        (Kleene.partialFixedPointProgram
          compiler
          bodyProgram)
        dynamicInput
        output)
boundedStateTerminationGivesPartialFixedPointTermination
    stepSystem
    initial
    compiler
    bodyProgram
    dynamicInput
    realization
    with Q2.boundedSelfReferenceHasTerminalState
           stepSystem
           initial
... | terminalState , terminalProof =
  terminalOutput realization terminalState
  ,
  Kleene.terminates-with
    (terminalRealizesFixedPointRun
      realization
      terminalState
      terminalProof)

------------------------------------------------------------------------
-- Clay-facing contradiction composition.
--
-- Under SAT in P, the candidate extracted from satP is exact.  If an
-- opposite-SAT partial body exists and its fixed-point execution is realized by
-- a Q2 whole-state decreasing system, Q2 forces termination while the existing
-- no-go theorem proves that termination impossible.
------------------------------------------------------------------------

realizedBoundedDescentContradictsExactSAT :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : Bridge.PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (compiler : Kleene.PartialDiagonalCompiler system)
    (body :
      Bridge.PartialSATDiagonalBody
        (NoGo.satPCandidate satP)
        system
        view
        dynamicInput)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState)
    (realization :
      BoundedFixedPointExecutionRealization
        stepSystem
        initial
        system
        compiler
        (Bridge.bodyProgram body)
        dynamicInput) →
  ⊥
realizedBoundedDescentContradictsExactSAT
    {dynamicInput = dynamicInput}
    satP
    compiler
    body
    stepSystem
    initial
    realization
    with boundedStateTerminationGivesPartialFixedPointTermination
           stepSystem
           initial
           compiler
           (Bridge.bodyProgram body)
           dynamicInput
           realization
... | output , terminates =
  NoGo.exactSATForcesPartialLiarFixedPointDivergence
    satP
    compiler
    body
    output
    terminates

------------------------------------------------------------------------
-- Research boundary.
--
-- The remaining contradiction-producing theorem is now localized precisely:
--
--   construct the special self-instantiation Q1 objects at every live state;
--   use them to define the total Q2 next-step system;
--   prove whole-state strict decrease;
--   prove terminal Q2 states realize the actual partial-Kleene run.
--
-- The first three are the quantitative closed-quotient theorem; the last is the
-- concrete universal-interpreter / specialization execution seam.  This file
-- does not manufacture either premise.
------------------------------------------------------------------------
