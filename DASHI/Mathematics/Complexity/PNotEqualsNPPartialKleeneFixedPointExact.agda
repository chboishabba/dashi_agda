module DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact where

------------------------------------------------------------------------
-- PARTIAL KLEENE-STYLE BEHAVIOURAL FIXED POINT
--
-- IMPORTANT CORRECTION TO THE TOTAL CONTROL MODEL
--
-- Classical universal computation is partial.  A fixed-point program may
-- diverge.  That fact is essential: if every quoted program were forced to
-- return a finite formula, a sufficiently expressive total system plus an
-- "output the opposite of D(output(q))" body would create a liar even against
-- the repository's constructive exact SAT decider.
--
-- Therefore the self-reference route must work over PARTIAL semantics.
--
-- This owner repeats the explicit specialization construction with:
--
--   run1 : Program -> Input -> Maybe Output
--   run2 : Program -> Program -> Input -> Maybe Output.
--
-- No fixed-point field is assumed.  Given executable specialization and
-- diagonal-compilation laws, we still construct:
--
--   p* = specialize d d
--
-- and prove equality of PARTIAL computations:
--
--   run1 p* x = run2 p p* x.
--
-- What does NOT follow is that either side terminates.  Termination is a
-- separate theorem and is the exact place where bounded/resource-aware
-- self-reference must pay new mathematics.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _≤_)
open import Data.Maybe.Base using (Maybe; just)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Partial specializing programming system.
------------------------------------------------------------------------

record PartialSpecializingProgramSystem : Set₁ where
  field
    Program : Set
    Input : Set
    Output : Set

    run1 :
      Program →
      Input →
      Maybe Output

    run2 :
      Program →
      Program →
      Input →
      Maybe Output

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

open PartialSpecializingProgramSystem public

------------------------------------------------------------------------
-- Partial diagonal compiler.
------------------------------------------------------------------------

record PartialDiagonalCompiler
    (system : PartialSpecializingProgramSystem) : Set₁ where
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

open PartialDiagonalCompiler public

------------------------------------------------------------------------
-- Concrete fixed-point program.
------------------------------------------------------------------------

partialFixedPointProgram :
  ∀ {system : PartialSpecializingProgramSystem} →
  PartialDiagonalCompiler system →
  Program system →
  Program system
partialFixedPointProgram
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
-- Main partial behavioral fixed-point theorem.
------------------------------------------------------------------------

partialFixedPointProgramCorrect :
  ∀ {system : PartialSpecializingProgramSystem}
    (compiler : PartialDiagonalCompiler system)
    (program : Program system)
    (input : Input system) →
  run1
    system
    (partialFixedPointProgram
      compiler
      program)
    input
  ≡
  run2
    system
    program
    (partialFixedPointProgram
      compiler
      program)
    input
partialFixedPointProgramCorrect
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
-- Termination is a SEPARATE witness.
------------------------------------------------------------------------

record TerminatesWith
    {system : PartialSpecializingProgramSystem}
    (program : Program system)
    (input : Input system)
    (output : Output system) : Set where
  constructor terminates-with
  field
    runResult :
      run1 system program input
      ≡ just output

open TerminatesWith public

partialFixedPointTerminationTransfersToBody :
  ∀ {system : PartialSpecializingProgramSystem}
    (compiler : PartialDiagonalCompiler system)
    (program : Program system)
    (input : Input system)
    (output : Output system) →
  TerminatesWith
    (partialFixedPointProgram compiler program)
    input
    output →
  run2
    system
    program
    (partialFixedPointProgram compiler program)
    input
  ≡ just output
partialFixedPointTerminationTransfersToBody
    compiler
    program
    input
    output
    terminates =
  trans
    (sym
      (partialFixedPointProgramCorrect
        compiler
        program
        input))
    (runResult terminates)

------------------------------------------------------------------------
-- Size-aware partial system.
------------------------------------------------------------------------

record SizedPartialSpecializingProgramSystem
    (system : PartialSpecializingProgramSystem) : Set₁ where
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

open SizedPartialSpecializingProgramSystem public

partialFixedPointProgramSizeBound :
  ∀ {system : PartialSpecializingProgramSystem}
    (sized :
      SizedPartialSpecializingProgramSystem
        system)
    (compiler : PartialDiagonalCompiler system)
    (program : Program system) →
  programSize sized
    (partialFixedPointProgram
      compiler
      program)
  ≤
  specializationSizeBound
    sized
    (programSize sized
      (diagonalize compiler program))
    (programSize sized
      (diagonalize compiler program))
partialFixedPointProgramSizeBound
    sized
    compiler
    program =
  specializeSize
    sized
    (diagonalize compiler program)
    (diagonalize compiler program)

------------------------------------------------------------------------
-- Research boundary.
--
-- The classical/partial fixed-point theorem now pays only semantic
-- self-reference:
--
--   run(p*) = run(body,p*).
--
-- It does NOT pay:
--
--   run(p*) = just formula.
--
-- For the P != NP route, proving bounded termination of p* with a concrete
-- formula is part of the resource-closing theorem.  This prevents ordinary
-- computability-level recursion from being silently promoted into a finite
-- SAT liar.
------------------------------------------------------------------------
