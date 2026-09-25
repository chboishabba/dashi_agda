module DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneToSelfDiagonalExact where

------------------------------------------------------------------------
-- PARTIAL BEHAVIOURAL FIXED POINT -> SAT SELF-DIAGONAL WITNESS
--
-- Correct partial-computation version of the SAT bridge.
--
-- A quoted program q may diverge.  The diagonal body is therefore required to
-- produce an opposite-SAT formula only when q terminates with a concrete Cook
-- formula output.
--
-- The Kleene fixed-point theorem supplies only:
--
--   run1 p* x = run2 body p* x
--
-- as equality of Maybe-valued computations.
--
-- To obtain an actual finite self-diagonal formula we additionally require:
--
--   run1 p* x = just fixedOutput.
--
-- That TERMINATION witness is intentionally explicit.  It is the exact
-- resource/totality debt ordinary computability-level self-reference does not
-- discharge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceBoundedSelfDiagonalExact as Self
import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene

------------------------------------------------------------------------
-- Formula view of terminating outputs.
------------------------------------------------------------------------

record PartialCookFormulaOutputView
    (system : Kleene.PartialSpecializingProgramSystem) : Set₁ where
  field
    asFormula :
      Kleene.Output system →
      Cook.BooleanFormula

open PartialCookFormulaOutputView public

------------------------------------------------------------------------
-- One body result for one TERMINATING quoted program.
------------------------------------------------------------------------

record PartialSATBodyResult
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    {system : Kleene.PartialSpecializingProgramSystem}
    (view : PartialCookFormulaOutputView system)
    (quotedOutput : Kleene.Output system)
    (bodyOutput : Kleene.Output system) : Set₁ where
  field
    satisfiableIfQuotedRejected :
      Direct.decide
        candidate
        (asFormula view quotedOutput)
      ≡ false →
      Cook.Satisfiable
        (asFormula view bodyOutput)

    quotedRejectedIfBodySatisfiable :
      Cook.Satisfiable
        (asFormula view bodyOutput) →
      Direct.decide
        candidate
        (asFormula view quotedOutput)
      ≡ false

open PartialSATBodyResult public

------------------------------------------------------------------------
-- Non-self-referential partial diagonal body.
------------------------------------------------------------------------

record PartialSATDiagonalBody
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (system : Kleene.PartialSpecializingProgramSystem)
    (view : PartialCookFormulaOutputView system)
    (dynamicInput : Kleene.Input system) : Set₁ where
  field
    bodyProgram :
      Kleene.Program system

    bodyOnTerminatingQuoted :
      (quoted : Kleene.Program system) →
      (quotedOutput : Kleene.Output system) →
      Kleene.run1
        system
        quoted
        dynamicInput
      ≡ just quotedOutput →
      Σ (Kleene.Output system)
        (λ bodyOutput →
          (Kleene.run2
            system
            bodyProgram
            quoted
            dynamicInput
           ≡ just bodyOutput)
          ×
          PartialSATBodyResult
            candidate
            view
            quotedOutput
            bodyOutput)

open PartialSATDiagonalBody public

------------------------------------------------------------------------
-- just is injective.
------------------------------------------------------------------------

justInjective :
  ∀ {A : Set} {left right : A} →
  just left ≡ just right →
  left ≡ right
justInjective refl =
  refl

------------------------------------------------------------------------
-- At a terminating fixed point, the body's output is the SAME fixed output.
------------------------------------------------------------------------

fixedBodyOutputEqualsFixedOutput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (compiler : Kleene.PartialDiagonalCompiler system)
    (body :
      PartialSATDiagonalBody
        candidate
        system
        view
        dynamicInput)
    (fixedOutput : Kleene.Output system)
    (fixedTerminates :
      Kleene.TerminatesWith
        (Kleene.partialFixedPointProgram
          compiler
          (bodyProgram body))
        dynamicInput
        fixedOutput) →
  let fixedProgram =
        Kleene.partialFixedPointProgram
          compiler
          (bodyProgram body)
      result =
        bodyOnTerminatingQuoted
          body
          fixedProgram
          fixedOutput
          (Kleene.runResult fixedTerminates)
  in
  proj₁ result ≡ fixedOutput
fixedBodyOutputEqualsFixedOutput
    {system = system}
    {dynamicInput = dynamicInput}
    compiler
    body
    fixedOutput
    fixedTerminates
    with
      bodyOnTerminatingQuoted
        body
        fixedProgram
        fixedOutput
        (Kleene.runResult fixedTerminates)
... | bodyOutput , bodyRun , semantics =
  justInjective
    (trans
      (sym bodyRun)
      fixedBodyRun)
  where
    fixedProgram :
      Kleene.Program system
    fixedProgram =
      Kleene.partialFixedPointProgram
        compiler
        (bodyProgram body)

    fixedBodyRun :
      Kleene.run2
        system
        (bodyProgram body)
        fixedProgram
        dynamicInput
      ≡ just fixedOutput
    fixedBodyRun =
      Kleene.partialFixedPointTerminationTransfersToBody
        compiler
        (bodyProgram body)
        dynamicInput
        fixedOutput
        fixedTerminates

------------------------------------------------------------------------
-- Main compiler.
------------------------------------------------------------------------

partialKleeneBodyAndTerminationGiveSelfDiagonalWitness :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system} →
  (compiler : Kleene.PartialDiagonalCompiler system) →
  (body :
    PartialSATDiagonalBody
      candidate
      system
      view
      dynamicInput) →
  (fixedOutput : Kleene.Output system) →
  Kleene.TerminatesWith
    (Kleene.partialFixedPointProgram
      compiler
      (bodyProgram body))
    dynamicInput
    fixedOutput →
  Self.SelfDiagonalSemanticWitness candidate
partialKleeneBodyAndTerminationGiveSelfDiagonalWitness
    {candidate = candidate}
    {system = system}
    {view = view}
    {dynamicInput = dynamicInput}
    compiler
    body
    fixedOutput
    fixedTerminates
    with
      bodyOnTerminatingQuoted
        body
        fixedProgram
        fixedOutput
        (Kleene.runResult fixedTerminates)
... | bodyOutput , bodyRun , semantics =
  Self.self-diagonal-semantic-witness
    fixedFormula
    satisfiableIfRejects
    rejectsIfSatisfiable
  where
    fixedProgram :
      Kleene.Program system
    fixedProgram =
      Kleene.partialFixedPointProgram
        compiler
        (bodyProgram body)

    outputEquality :
      bodyOutput ≡ fixedOutput
    outputEquality =
      justInjective
        (trans
          (sym bodyRun)
          (Kleene.partialFixedPointTerminationTransfersToBody
            compiler
            (bodyProgram body)
            dynamicInput
            fixedOutput
            fixedTerminates))

    fixedFormula :
      Cook.BooleanFormula
    fixedFormula =
      asFormula view fixedOutput

    satisfiableIfRejects :
      Direct.decide candidate fixedFormula
      ≡ false →
      Cook.Satisfiable fixedFormula
    satisfiableIfRejects rejected =
      subst
        (λ output →
          Cook.Satisfiable
            (asFormula view output))
        outputEquality
        (satisfiableIfQuotedRejected
          semantics
          rejected)

    rejectsIfSatisfiable :
      Cook.Satisfiable fixedFormula →
      Direct.decide candidate fixedFormula
      ≡ false
    rejectsIfSatisfiable fixedSat =
      quotedRejectedIfBodySatisfiable
        semantics
        (subst
          (λ output →
            Cook.Satisfiable
              (asFormula view output))
          (sym outputEquality)
          fixedSat)

------------------------------------------------------------------------
-- Immediate failure theorem.
------------------------------------------------------------------------

partialKleeneBodyAndTerminationGiveFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.PartialSpecializingProgramSystem}
    {view : PartialCookFormulaOutputView system}
    {dynamicInput : Kleene.Input system} →
  (compiler : Kleene.PartialDiagonalCompiler system) →
  (body :
    PartialSATDiagonalBody
      candidate
      system
      view
      dynamicInput) →
  (fixedOutput : Kleene.Output system) →
  Kleene.TerminatesWith
    (Kleene.partialFixedPointProgram
      compiler
      (bodyProgram body))
    dynamicInput
    fixedOutput →
  Direct.SATDecisionFailure candidate
partialKleeneBodyAndTerminationGiveFailure
    compiler
    body
    fixedOutput
    fixedTerminates =
  Self.selfDiagonalSemanticWitnessGivesFailure
    (partialKleeneBodyAndTerminationGiveSelfDiagonalWitness
      compiler
      body
      fixedOutput
      fixedTerminates)

------------------------------------------------------------------------
-- Research consequence.
--
-- The route is now split at the mathematically correct seam:
--
--   partial recursion theorem                    PAID
--   non-self-referential body on terminating q  OPEN/constructive target
--   bounded termination of the fixed program    OPEN/critical
--   resource-closing quotient / representatives OPEN/critical
--
-- Classical recursion alone does not create a finite SAT liar.  The decisive
-- theorem must force the particular fixed program used by the SAT body to
-- terminate within the self-size/polynomial resource budget.
------------------------------------------------------------------------
