module DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact where

------------------------------------------------------------------------
-- EXPLICIT KLEENE-STYLE BEHAVIOURAL FIXED POINT
--
-- This is NOT an axiom saying "a fixed point exists".
--
-- A program system supplies:
--
--   run1       : unary program semantics
--   run2       : two-argument program semantics
--   specialize : concrete s-1-1 style partial evaluator
--
-- with the executable law
--
--   run1 (specialize p q) x = run2 p q x.
--
-- A diagonal compiler supplies, for every binary program p, a concrete program
-- d = diagonalize p satisfying
--
--   run2 d q x = run2 p (specialize q q) x.
--
-- Then the fixed-point program is CONSTRUCTED:
--
--   p* = specialize d d
--
-- and we prove
--
--   run1 p* x = run2 p p* x.
--
-- This is the exact program-level self-reference shape needed after the raw
-- formula-code fixed point was ruled out.
--
-- RESOURCE BOUNDARY:
--
-- Program size accounting is retained separately.  The classical semantic
-- theorem does not by itself prove polynomial runtime or a small SAT formula.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

------------------------------------------------------------------------
-- Specializing programming system.
------------------------------------------------------------------------

record SpecializingProgramSystem : Set₁ where
  field
    Program : Set
    Input : Set
    Output : Set

    run1 :
      Program →
      Input →
      Output

    run2 :
      Program →
      Program →
      Input →
      Output

    specialize :
      Program →
      Program →
      Program

    specializeCorrect :
      (program static : Program) →
      (dynamic : Input) →
      run1
        (specialize program static)
        dynamic
      ≡
      run2
        program
        static
        dynamic

open SpecializingProgramSystem public

------------------------------------------------------------------------
-- Explicit diagonal compiler.
--
-- This is the constructive content normally obtained from computability /
-- program-generation closure in the classical recursion-theorem proof.
------------------------------------------------------------------------

record DiagonalCompiler
    (system : SpecializingProgramSystem) : Set₁ where
  field
    diagonalize :
      Program system →
      Program system

    diagonalizeCorrect :
      (program query : Program system) →
      (input : Input system) →
      run2
        system
        (diagonalize program)
        query
        input
      ≡
      run2
        system
        program
        (specialize system query query)
        input

open DiagonalCompiler public

------------------------------------------------------------------------
-- Concrete fixed-point construction.
------------------------------------------------------------------------

fixedPointProgram :
  ∀ {system : SpecializingProgramSystem} →
  DiagonalCompiler system →
  Program system →
  Program system
fixedPointProgram
    {system}
    compiler
    program =
  specialize
    system
    diagonal
    diagonal
  where
    diagonal :
      Program system
    diagonal =
      diagonalize compiler program

------------------------------------------------------------------------
-- Main behavioural fixed-point theorem.
------------------------------------------------------------------------

fixedPointProgramCorrect :
  ∀ {system : SpecializingProgramSystem}
    (compiler : DiagonalCompiler system)
    (program : Program system)
    (input : Input system) →
  run1
    system
    (fixedPointProgram compiler program)
    input
  ≡
  run2
    system
    program
    (fixedPointProgram compiler program)
    input
fixedPointProgramCorrect
    {system}
    compiler
    program
    input =
  trans
    (specializeCorrect
      system
      diagonal
      diagonal
      input)
    (diagonalizeCorrect
      compiler
      program
      diagonal
      input)
  where
    diagonal :
      Program system
    diagonal =
      diagonalize compiler program

------------------------------------------------------------------------
-- Size-aware extension.
------------------------------------------------------------------------

record SizedSpecializingProgramSystem
    (system : SpecializingProgramSystem) : Set₁ where
  field
    programSize :
      Program system →
      Nat

    specializationSizeBound :
      Nat →
      Nat →
      Nat

    specializeSize :
      (program static : Program system) →
      programSize
        (specialize system program static)
      ≤
      specializationSizeBound
        (programSize program)
        (programSize static)

open SizedSpecializingProgramSystem public

fixedPointProgramSizeBound :
  ∀ {system : SpecializingProgramSystem}
    (sized : SizedSpecializingProgramSystem system)
    (compiler : DiagonalCompiler system)
    (program : Program system) →
  programSize sized
    (fixedPointProgram compiler program)
  ≤
  specializationSizeBound
    sized
    (programSize sized
      (diagonalize compiler program))
    (programSize sized
      (diagonalize compiler program))
fixedPointProgramSizeBound
    sized
    compiler
    program =
  specializeSize
    sized
    (diagonalize compiler program)
    (diagonalize compiler program)

------------------------------------------------------------------------
-- Explicit statement of what remains unpaid for the SAT route.
------------------------------------------------------------------------

record BoundedFixedPointClosure
    {system : SpecializingProgramSystem}
    (sized : SizedSpecializingProgramSystem system)
    (compiler : DiagonalCompiler system)
    (program : Program system) : Set₁ where
  field
    fixedPointBudget : Nat

    fixedPointFitsBudget :
      programSize sized
        (fixedPointProgram compiler program)
      ≤ fixedPointBudget

    -- Intentionally no runtime/circuit/SAT claim is manufactured here.

open BoundedFixedPointClosure public

------------------------------------------------------------------------
-- Research consequence.
--
-- The raw equation
--
--   source = code(generatedFormula(source))
--
-- is unnecessary.  A concrete specializer + diagonal compiler yields the
-- correct BEHAVIOURAL fixed point by construction.
--
-- The new SAT-specific obligations are therefore:
--
--   1. instantiate this program system on a concrete machine model that can
--      consume/produce the Cook-formula binary code;
--   2. construct its diagonal compiler without invoking SAT truth;
--   3. prove specialization/diagonalization generation and execution costs
--      fit the polynomial/self-size budget;
--   4. compose the resulting behavioral fixed point with the already-built
--      restriction quotient / strict representative closure.
--
-- Those are stronger than classical computability-level recursion and remain
-- open.
------------------------------------------------------------------------
