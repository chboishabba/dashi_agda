module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact where

------------------------------------------------------------------------
-- FINITE SELF-SPECIALIZING PARTIAL PROGRAM CODE
--
-- EXEC-REALIZE needs an actual program syntax, not another record whose
-- specialize/diagonal laws are assumptions.
--
-- This owner provides the smallest honest code calculus needed by the existing
-- partial-Kleene theorem.
--
-- Program syntax is a finite tree:
--
--   primitive a
--   specialized p q
--   diagonalized p
--
-- Its interpreter is executable by structural recursion.  Specialization and
-- diagonalization are syntax constructors, so the two s-m-n / diagonal laws
-- reduce by definition:
--
--   run1 (specialized p q) x
--     = run2 p q x
--
--   run2 (diagonalized p) q x
--     = run2 p (specialized q q) x.
--
-- Only primitive instruction semantics are supplied by the client.  In
-- particular, this file does NOT hide SAT or the Q1 theorem in the interpreter.
-- It pays the standard self-specialization machinery around a finite primitive
-- code set.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Maybe.Base using (Maybe; nothing)

import DASHI.Mathematics.Complexity.PNotEqualsNPPartialKleeneFixedPointExact as Kleene

------------------------------------------------------------------------
-- Finite syntax.
------------------------------------------------------------------------

data Program (Primitive : Set) : Set where
  primitive :
    Primitive →
    Program Primitive

  specialized :
    Program Primitive →
    Program Primitive →
    Program Primitive

  diagonalized :
    Program Primitive →
    Program Primitive

------------------------------------------------------------------------
-- Primitive execution kernel.
--
-- Binary primitive semantics receives the literal quoted program argument.
------------------------------------------------------------------------

record PrimitiveSemantics
    (Primitive Input Output : Set) : Set₁ where
  field
    runPrimitive1 :
      Primitive →
      Input →
      Maybe Output

    runPrimitive2 :
      Primitive →
      Program Primitive →
      Input →
      Maybe Output

open PrimitiveSemantics public

------------------------------------------------------------------------
-- Structural interpreter.
------------------------------------------------------------------------

mutual
  run1 :
    ∀ {Primitive Input Output : Set} →
    PrimitiveSemantics Primitive Input Output →
    Program Primitive →
    Input →
    Maybe Output
  run1 semantics (primitive atom) input =
    runPrimitive1 semantics atom input
  run1 semantics (specialized program static) input =
    run2 semantics program static input
  run1 semantics (diagonalized program) input =
    nothing

  run2 :
    ∀ {Primitive Input Output : Set} →
    PrimitiveSemantics Primitive Input Output →
    Program Primitive →
    Program Primitive →
    Input →
    Maybe Output
  run2 semantics (primitive atom) quoted input =
    runPrimitive2 semantics atom quoted input
  run2 semantics (specialized program static) quoted input =
    nothing
  run2 semantics (diagonalized program) quoted input =
    run2 semantics
      program
      (specialized quoted quoted)
      input

------------------------------------------------------------------------
-- Executable s-m-n and diagonal constructors.
------------------------------------------------------------------------

specialize :
  ∀ {Primitive : Set} →
  Program Primitive →
  Program Primitive →
  Program Primitive
specialize =
  specialized

diagonalize :
  ∀ {Primitive : Set} →
  Program Primitive →
  Program Primitive
diagonalize =
  diagonalized

specializeCorrect :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output)
    (program static : Program Primitive)
    (dynamic : Input) →
  run1 semantics
    (specialize program static)
    dynamic
  ≡
  run2 semantics
    program
    static
    dynamic
specializeCorrect semantics program static dynamic =
  refl

diagonalizeCorrect :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output)
    (program query : Program Primitive)
    (input : Input) →
  run2 semantics
    (diagonalize program)
    query
    input
  ≡
  run2 semantics
    program
    (specialize query query)
    input
diagonalizeCorrect semantics program query input =
  refl

------------------------------------------------------------------------
-- Literal instantiation of the repository partial-Kleene interface.
------------------------------------------------------------------------

finiteCodePartialSystem :
  ∀ {Primitive Input Output : Set} →
  PrimitiveSemantics Primitive Input Output →
  Kleene.PartialSpecializingProgramSystem
finiteCodePartialSystem {Primitive} {Input} {Output} semantics =
  record
    { Kleene.Program =
        Program Primitive
    ; Kleene.Input =
        Input
    ; Kleene.Output =
        Output
    ; Kleene.run1 =
        run1 semantics
    ; Kleene.run2 =
        run2 semantics
    ; Kleene.specialize =
        specialize
    ; Kleene.specializeCorrect =
        specializeCorrect semantics
    }

finiteCodeDiagonalCompiler :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output) →
  Kleene.PartialDiagonalCompiler
    (finiteCodePartialSystem semantics)
finiteCodeDiagonalCompiler semantics =
  record
    { Kleene.diagonalize =
        diagonalize
    ; Kleene.diagonalizeCorrect =
        diagonalizeCorrect semantics
    }

------------------------------------------------------------------------
-- Exact syntax size.
------------------------------------------------------------------------

programSize :
  ∀ {Primitive : Set} →
  Program Primitive →
  Nat
programSize (primitive atom) =
  suc 0
programSize (specialized program static) =
  suc
    (programSize program
      + programSize static)
programSize (diagonalized program) =
  suc (programSize program)

specializationSizeBound :
  Nat → Nat → Nat
specializationSizeBound left right =
  suc (left + right)

specializeSizeExact :
  ∀ {Primitive : Set}
    (program static : Program Primitive) →
  programSize
    (specialize program static)
  ≡
  specializationSizeBound
    (programSize program)
    (programSize static)
specializeSizeExact program static =
  refl

specializeSize :
  ∀ {Primitive : Set}
    (program static : Program Primitive) →
  programSize
    (specialize program static)
  ≤
  specializationSizeBound
    (programSize program)
    (programSize static)
specializeSize program static =
  NatP.≤-refl

------------------------------------------------------------------------
-- Sized partial-system instance.
------------------------------------------------------------------------

finiteCodeSizedPartialSystem :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output) →
  Kleene.SizedPartialSpecializingProgramSystem
    (finiteCodePartialSystem semantics)
finiteCodeSizedPartialSystem semantics =
  record
    { Kleene.programSize =
        programSize
    ; Kleene.specializationSizeBound =
        specializationSizeBound
    ; Kleene.specializeSize =
        specializeSize
    }

------------------------------------------------------------------------
-- Exact fixed-point syntax for a primitive binary body.
------------------------------------------------------------------------

primitiveBodyFixedPoint :
  ∀ {Primitive : Set} →
  Primitive →
  Program Primitive
primitiveBodyFixedPoint body =
  specialize
    (diagonalize (primitive body))
    (diagonalize (primitive body))

primitiveBodyFixedPointIsKleeneFixedPoint :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output)
    (body : Primitive) →
  primitiveBodyFixedPoint body
  ≡
  Kleene.partialFixedPointProgram
    (finiteCodeDiagonalCompiler semantics)
    (primitive body)
primitiveBodyFixedPointIsKleeneFixedPoint semantics body =
  refl

primitiveBodyFixedPointRun :
  ∀ {Primitive Input Output : Set}
    (semantics : PrimitiveSemantics Primitive Input Output)
    (body : Primitive)
    (input : Input) →
  run1 semantics
    (primitiveBodyFixedPoint body)
    input
  ≡
  runPrimitive2 semantics
    body
    (primitiveBodyFixedPoint body)
    input
primitiveBodyFixedPointRun semantics body input =
  refl

primitiveBodyFixedPointSize :
  ∀ {Primitive : Set}
    (body : Primitive) →
  programSize (primitiveBodyFixedPoint body)
  ≡
  suc
    (suc (suc 0)
      + suc (suc 0))
primitiveBodyFixedPointSize body =
  refl

------------------------------------------------------------------------
-- EXEC-REALIZE consequence.
--
-- Specialization, diagonalization and their execution equations are no longer
-- fields in this concrete program system.  They are executable constructors
-- with definitional correctness.
--
-- The remaining execution seam is now ONLY the primitive body:
--
--   runPrimitive2 body fixedPoint input = just output.
--
-- That is precisely where the special self-instantiation/Q1 computation must be
-- implemented.  No generic universal-simulation premise remains between the
-- finite code syntax and the repository's PartialKleene theorem.
------------------------------------------------------------------------
