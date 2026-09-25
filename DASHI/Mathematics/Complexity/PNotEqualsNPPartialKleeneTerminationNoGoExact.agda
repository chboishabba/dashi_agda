module DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact where

------------------------------------------------------------------------
-- EXACT SAT CORRECTNESS FORCES THE LIAR FIXED POINT TO DIVERGE
--
-- Existing owners:
--
--   PNotEqualsNPPartialKleeneFixedPointExact
--   PNotEqualsNPPartialKleeneToSelfDiagonalExact
--   PNotEqualsNPDirectSATLowerBoundExact
--
-- together already imply an important theorem which should be explicit.
--
-- Assume the contradiction hypothesis:
--
--   satP : SAT in P.
--
-- Let candidate be the exact polynomial SAT decider extracted from satP.
-- Suppose a partial Kleene body has the required "opposite SAT" semantics for
-- every terminating quoted program.
--
-- Then the Kleene fixed-point program CANNOT terminate with any finite output.
--
-- Proof:
--
--   fixed point terminates
--      -> PartialKleene bridge constructs SelfDiagonalSemanticWitness
--      -> SATDecisionFailure(candidate)
--      -> contradiction with exact correctness of satP.
--
-- Therefore ordinary partial recursion does not leave only a small engineering
-- termination debt.  Under exact SAT correctness, divergence is forced unless
-- one proves genuinely new structure strong enough to cross the lower-bound
-- wall.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneToSelfDiagonalExact as Bridge

------------------------------------------------------------------------
-- Canonical polynomial SAT candidate extracted from SAT in P.
------------------------------------------------------------------------

satPCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  Direct.PolynomialSATDeciderCandidate cost
satPCandidate =
  Direct.inPToPolynomialSATDeciderCandidate

------------------------------------------------------------------------
-- Main divergence theorem.
------------------------------------------------------------------------

exactSATForcesPartialLiarFixedPointDivergence :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : Bridge.PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (compiler : Kleene.PartialDiagonalCompiler system)
    (body :
      Bridge.PartialSATDiagonalBody
        (satPCandidate satP)
        system
        view
        dynamicInput)
    (fixedOutput : Kleene.Output system) →
  Kleene.TerminatesWith
    (Kleene.partialFixedPointProgram
      compiler
      (Bridge.bodyProgram body))
    dynamicInput
    fixedOutput →
  ⊥
exactSATForcesPartialLiarFixedPointDivergence
    satP
    compiler
    body
    fixedOutput
    fixedTerminates =
  Direct.failureContradictsCorrectSATDecision
    satP
    (Bridge.partialKleeneBodyAndTerminationGiveFailure
      compiler
      body
      fixedOutput
      fixedTerminates)

------------------------------------------------------------------------
-- Stronger pointwise formulation: no output can witness termination.
------------------------------------------------------------------------

NoFixedPointOutput :
  ∀ {system : Kleene.PartialSpecializingProgramSystem} →
  (program : Kleene.Program system) →
  (input : Kleene.Input system) →
  Set
NoFixedPointOutput {system} program input =
  (output : Kleene.Output system) →
  Kleene.TerminatesWith
    program
    input
    output →
  ⊥

exactSATForcesNoPartialLiarFixedPointOutput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : Bridge.PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (compiler : Kleene.PartialDiagonalCompiler system)
    (body :
      Bridge.PartialSATDiagonalBody
        (satPCandidate satP)
        system
        view
        dynamicInput) →
  NoFixedPointOutput
    (Kleene.partialFixedPointProgram
      compiler
      (Bridge.bodyProgram body))
    dynamicInput
exactSATForcesNoPartialLiarFixedPointOutput
    satP
    compiler
    body
    fixedOutput =
  exactSATForcesPartialLiarFixedPointDivergence
    satP
    compiler
    body
    fixedOutput

------------------------------------------------------------------------
-- Research consequence.
--
-- The current bounded-self-reference route has a precise obstruction:
--
--   partial recursion theorem                 PAID
--   exact opposite-SAT body on terminating q ASSUMED/constructive target
--   fixed-point termination                  FORCED FALSE under SAT in P
--
-- unless additional mathematics invalidates the contradiction hypothesis.
--
-- Thus a future "resource-closing quotient forces termination" theorem is not
-- merely another compiler result.  Combined with the body semantics, it IS a
-- direct contradiction with SAT in P and therefore lies on the actual Clay
-- lower-bound frontier.
------------------------------------------------------------------------
