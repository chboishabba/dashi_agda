module DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCodeClayClosureExact where

------------------------------------------------------------------------
-- Q1 -> CONCRETE FINITE-CODE LIAR -> CLAY CONTRADICTION
--
-- EXEC-REALIZE is paid by:
--
--   PNotEqualsNPFiniteSelfSpecializingCodeExact
--   PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact.
--
-- This owner deliberately introduces NO new interpreter boundary.
--
-- It asks only for the remaining Q1 semantic fact on the already-built Q2
-- step system:
--
-- for every quoted finite-code program which terminates with formula phi,
-- the canonical Q2 terminal formula A has exactly the opposite-SAT relation
-- required by the candidate:
--
--   D(phi)=false -> SAT(A)
--   SAT(A)        -> D(phi)=false.
--
-- From that one premise we construct the repository's PartialSATDiagonalBody,
-- use the concrete finite-code Q2 execution realization, and derive the existing
-- exact-SAT contradiction.
--
-- Hence after this file the remaining Clay burden is visibly Q1:
--
--   construct the self-instantiation Q2 system + prove the opposite-SAT
--   terminal semantics while satisfying the all-overhead strict descent at
--   every live state.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact as Exec
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneToSelfDiagonalExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneTerminationNoGoExact as NoGo
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedStateToPartialKleeneTerminationExact as Closure

------------------------------------------------------------------------
-- Identity formula view: Q2 finite-code outputs ARE ordinary Cook formulas.
------------------------------------------------------------------------

q2CookOutputView :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem) →
  (initial : Q2.BoundedSelfReferenceState) →
  Bridge.PartialCookFormulaOutputView
    (Exec.q2PartialSystem stepSystem initial)
q2CookOutputView stepSystem initial =
  record
    { Bridge.asFormula =
        λ formula → formula
    }

------------------------------------------------------------------------
-- The sole remaining semantic premise.
------------------------------------------------------------------------

Q1OppositeSATTerminalSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  Set₁
Q1OppositeSATTerminalSemantics
    candidate
    stepSystem
    initial =
  (quoted : Code.Program Exec.Q2Primitive) →
  (quotedOutput : Cook.BooleanFormula) →
  Kleene.run1
    (Exec.q2PartialSystem stepSystem initial)
    quoted
    tt
  ≡
  just quotedOutput →
  (Direct.decide candidate quotedOutput ≡ false →
    Cook.Satisfiable
      (Exec.canonicalTerminalFormula
        stepSystem
        initial))
  ×
  (Cook.Satisfiable
      (Exec.canonicalTerminalFormula
        stepSystem
        initial) →
    Direct.decide candidate quotedOutput ≡ false)

------------------------------------------------------------------------
-- Q1 semantics constructs the exact PartialSATDiagonalBody.
------------------------------------------------------------------------

q1SemanticsBuildsPartialDiagonalBody :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  Q1OppositeSATTerminalSemantics
    candidate
    stepSystem
    initial →
  Bridge.PartialSATDiagonalBody
    candidate
    (Exec.q2PartialSystem stepSystem initial)
    (q2CookOutputView stepSystem initial)
    tt
q1SemanticsBuildsPartialDiagonalBody
    candidate
    stepSystem
    initial
    q1Semantics =
  record
    { Bridge.bodyProgram =
        Exec.q2BodyProgram
    ; Bridge.bodyOnTerminatingQuoted =
        bodyOnTerminatingQuoted
    }
  where
    bodyOnTerminatingQuoted :
      (quoted : Code.Program Exec.Q2Primitive) →
      (quotedOutput : Cook.BooleanFormula) →
      Kleene.run1
        (Exec.q2PartialSystem stepSystem initial)
        quoted
        tt
      ≡
      just quotedOutput →
      Σ Cook.BooleanFormula
        (λ bodyOutput →
          (Kleene.run2
            (Exec.q2PartialSystem stepSystem initial)
            Exec.q2BodyProgram
            quoted
            tt
           ≡ just bodyOutput)
          ×
          Bridge.PartialSATBodyResult
            candidate
            (q2CookOutputView stepSystem initial)
            quotedOutput
            bodyOutput)
    bodyOnTerminatingQuoted
        quoted
        quotedOutput
        quotedTerminates =
      Exec.canonicalTerminalFormula
          stepSystem
          initial
      ,
      refl
      ,
      record
        { Bridge.satisfiableIfQuotedRejected =
            proj₁
              (q1Semantics
                quoted
                quotedOutput
                quotedTerminates)
        ; Bridge.quotedRejectedIfBodySatisfiable =
            proj₂
              (q1Semantics
                quoted
                quotedOutput
                quotedTerminates)
        }

------------------------------------------------------------------------
-- Final finite-code contradiction.
------------------------------------------------------------------------

q1FiniteCodeContradictsSATInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  Q1OppositeSATTerminalSemantics
    (NoGo.satPCandidate satP)
    stepSystem
    initial →
  ⊥
q1FiniteCodeContradictsSATInP
    satP
    stepSystem
    initial
    q1Semantics =
  Closure.realizedBoundedDescentContradictsExactSAT
    satP
    (Exec.q2DiagonalCompiler
      stepSystem
      initial)
    body
    stepSystem
    initial
    (Exec.q2FiniteCodeExecutionRealization
      stepSystem
      initial)
  where
    body :
      Bridge.PartialSATDiagonalBody
        (NoGo.satPCandidate satP)
        (Exec.q2PartialSystem stepSystem initial)
        (q2CookOutputView stepSystem initial)
        tt
    body =
      q1SemanticsBuildsPartialDiagonalBody
        (NoGo.satPCandidate satP)
        stepSystem
        initial
        q1Semantics

------------------------------------------------------------------------
-- CLAY-FACING FRONTIER
--
-- No interpreter/s-m-n/diagonal/termination/realization field remains in the
-- final theorem above.
--
-- The live theorem search is now exactly:
--
--   under SAT in P, construct the special root-scoped Q2 system from the
--   candidate's finite self-instantiation data such that
--
--     * every live Q1 authority step satisfies the all-overhead strict budget;
--     * its canonical terminal formula satisfies
--       Q1OppositeSATTerminalSemantics.
--
-- Supplying those facts to q1FiniteCodeContradictsSATInP produces bottom, and
-- the existing Direct/Clay compiler turns the universal version into SAT notin P.
------------------------------------------------------------------------
