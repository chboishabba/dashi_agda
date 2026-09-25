module DASHI.Mathematics.Complexity.PNotEqualsNPKleeneToSelfDiagonalBridgeExact where

------------------------------------------------------------------------
-- BEHAVIOURAL KLEENE FIXED POINT -> SAT SELF-DIAGONAL WITNESS
--
-- Existing:
--   PNotEqualsNPKleeneSpecializationFixedPointExact
--
-- constructs, from a concrete specializer + diagonal compiler,
--
--   p* = specialize d d
--
-- with
--
--   run1 p* x = run2 p p* x.
--
-- This owner supplies the exact SAT-facing compiler.
--
-- The NON-SELF-REFERENTIAL body obligation is:
--
--   for every quoted program q,
--
--   SAT(run2 p q x)
--      iff
--   candidate rejects run1 q x.
--
-- This is an ordinary two-argument program/compiler property.  Applying the
-- behavioral fixed point to p turns q into p* automatically and yields:
--
--   SAT(phi) iff candidate rejects phi,
--
-- where phi = run1 p* x.
--
-- Thus the fixed-point semantics no longer appears as an open field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceBoundedSelfDiagonalExact as Self
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact as Kleene

------------------------------------------------------------------------
-- Formula-producing program system.
--
-- We retain the generic program-system Input carrier.  At one selected dynamic
-- input x, run1/run2 outputs must literally be Cook BooleanFormula values.
------------------------------------------------------------------------

record CookFormulaOutputView
    (system : Kleene.SpecializingProgramSystem) : Set₁ where
  field
    asFormula :
      Kleene.Output system →
      Cook.BooleanFormula

open CookFormulaOutputView public

------------------------------------------------------------------------
-- Non-self-referential diagonal body.
------------------------------------------------------------------------

record SATDiagonalBody
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (system : Kleene.SpecializingProgramSystem)
    (view : CookFormulaOutputView system)
    (dynamicInput : Kleene.Input system) : Set₁ where
  field
    bodyProgram :
      Kleene.Program system

    satisfiableIfQuotedProgramRejected :
      (quoted : Kleene.Program system) →
      Direct.decide
        candidate
        (asFormula view
          (Kleene.run1 system
            quoted
            dynamicInput))
      ≡ false →
      Cook.Satisfiable
        (asFormula view
          (Kleene.run2 system
            bodyProgram
            quoted
            dynamicInput))

    rejectsQuotedProgramIfBodySatisfiable :
      (quoted : Kleene.Program system) →
      Cook.Satisfiable
        (asFormula view
          (Kleene.run2 system
            bodyProgram
            quoted
            dynamicInput)) →
      Direct.decide
        candidate
        (asFormula view
          (Kleene.run1 system
            quoted
            dynamicInput))
      ≡ false

open SATDiagonalBody public

------------------------------------------------------------------------
-- Formula equality induced by the behavioral fixed point.
------------------------------------------------------------------------

fixedPointFormulaEquality :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system}
    (compiler : Kleene.DiagonalCompiler system)
    (body : SATDiagonalBody
      candidate system view dynamicInput) →
  asFormula view
    (Kleene.run1 system
      (Kleene.fixedPointProgram
        compiler
        (bodyProgram body))
      dynamicInput)
  ≡
  asFormula view
    (Kleene.run2 system
      (bodyProgram body)
      (Kleene.fixedPointProgram
        compiler
        (bodyProgram body))
      dynamicInput)
fixedPointFormulaEquality
    compiler
    body =
  congruence
    (Kleene.fixedPointProgramCorrect
      compiler
      (bodyProgram body)
      _)
  where
    congruence :
      ∀ {left right : Kleene.Output _} →
      left ≡ right →
      asFormula _ left
      ≡ asFormula _ right
    congruence refl =
      refl

------------------------------------------------------------------------
-- Main compiler: behavioral fixed point -> SelfDiagonalSemanticWitness.
------------------------------------------------------------------------

kleeneBodyGivesSelfDiagonalSemanticWitness :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system} →
  (compiler : Kleene.DiagonalCompiler system) →
  (body : SATDiagonalBody
    candidate
    system
    view
    dynamicInput) →
  Self.SelfDiagonalSemanticWitness candidate
kleeneBodyGivesSelfDiagonalSemanticWitness
    {candidate = candidate}
    {system = system}
    {view = view}
    {dynamicInput = dynamicInput}
    compiler
    body =
  Self.self-diagonal-semantic-witness
    fixedFormula
    satisfiableIfRejects
    rejectsIfSatisfiable
  where
    fixedProgram :
      Kleene.Program system
    fixedProgram =
      Kleene.fixedPointProgram
        compiler
        (bodyProgram body)

    fixedFormula :
      Cook.BooleanFormula
    fixedFormula =
      asFormula view
        (Kleene.run1 system
          fixedProgram
          dynamicInput)

    bodyFormula :
      Cook.BooleanFormula
    bodyFormula =
      asFormula view
        (Kleene.run2 system
          (bodyProgram body)
          fixedProgram
          dynamicInput)

    formulasEqual :
      fixedFormula ≡ bodyFormula
    formulasEqual =
      fixedPointFormulaEquality
        compiler
        body

    satisfiableIfRejects :
      Direct.decide candidate fixedFormula
      ≡ false →
      Cook.Satisfiable fixedFormula
    satisfiableIfRejects rejected =
      subst
        Cook.Satisfiable
        (sym formulasEqual)
        (satisfiableIfQuotedProgramRejected
          body
          fixedProgram
          rejected)

    rejectsIfSatisfiable :
      Cook.Satisfiable fixedFormula →
      Direct.decide candidate fixedFormula
      ≡ false
    rejectsIfSatisfiable fixedSat =
      rejectsQuotedProgramIfBodySatisfiable
        body
        fixedProgram
        (subst
          Cook.Satisfiable
          formulasEqual
          fixedSat)

------------------------------------------------------------------------
-- Immediate direct failure compiler.
------------------------------------------------------------------------

kleeneBodyGivesSATDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : Kleene.SpecializingProgramSystem}
    {view : CookFormulaOutputView system}
    {dynamicInput : Kleene.Input system} →
  Kleene.DiagonalCompiler system →
  SATDiagonalBody
    candidate
    system
    view
    dynamicInput →
  Direct.SATDecisionFailure candidate
kleeneBodyGivesSATDecisionFailure
    compiler
    body =
  Self.selfDiagonalSemanticWitnessGivesFailure
    (kleeneBodyGivesSelfDiagonalSemanticWitness
      compiler
      body)

------------------------------------------------------------------------
-- Research consequence.
--
-- The self-referential semantic equation itself is now mechanically compiled
-- from two ordinary ingredients:
--
--   A. a real program specializer/diagonal compiler;
--   B. a non-self-referential SAT diagonal body for arbitrary quoted q.
--
-- Ingredient B is the concrete target for the existing machine->Cook-Levin
-- stack: compose "run q to obtain a formula" with "run candidate D on that
-- formula and accept iff D rejects".
--
-- Resource closure remains separate: program generation, execution of q/D,
-- quotient construction and final formula size must still fit the polynomial
-- fixed-point budget.
------------------------------------------------------------------------
