module DASHI.Mathematics.Complexity.PNotEqualsNPExecutableCodeSingletonNoGoExact where

------------------------------------------------------------------------
-- GENERIC EXECUTABLE-CODE REFINEMENT STILL DOES NOT FORCE QUOTABLE PROGRAMS
--
-- PNotEqualsNPExecutablePolynomialCostRefinementExact adds:
--
--   Code : Set
--   code : Code
--   run  : Code -> Word -> Bool
--
-- but does not require Code to be finite/serializable or `run` to be the
-- semantics of a fixed finite interpreter.  Consequently every extensional
-- decider has the singleton realization:
--
--   Code = Unit
--   code = tt
--   run tt = decider.
--
-- Thus the generic executable refinement alone does not solve A0 quotation.
-- The literal deterministic concrete-tape bit carrier is genuinely stronger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as Exec

------------------------------------------------------------------------
-- Trivial executable wrappers.
------------------------------------------------------------------------

trivialMapCode :
  ∀ {Word : Set}
    (map : Word → Word) →
  Exec.ExecutableMapCode map
trivialMapCode map = record
  { Exec.Code = ⊤
  ; Exec.code = tt
  ; Exec.run = λ unit word → map word
  ; Exec.runExact = λ word → refl
  ; Exec.codeSize = λ unit → zero
  }

trivialDeciderCode :
  ∀ {Word : Set}
    (decider : Word → Bool) →
  Exec.ExecutableDeciderCode decider
trivialDeciderCode decider = record
  { Exec.Code = ⊤
  ; Exec.code = tt
  ; Exec.run = λ unit word → decider word
  ; Exec.runExact = λ word → refl
  ; Exec.codeSize = λ unit → zero
  }

trivialVerifierCode :
  ∀ {Word Certificate : Set}
    (verifier : Word → Certificate → Bool) →
  Exec.ExecutableVerifierCode verifier
trivialVerifierCode verifier = record
  { Exec.Code = ⊤
  ; Exec.code = tt
  ; Exec.run = λ unit word certificate → verifier word certificate
  ; Exec.runExact = λ word certificate → refl
  ; Exec.codeSize = λ unit → zero
  }

------------------------------------------------------------------------
-- The closure requirements can also be paid trivially.
------------------------------------------------------------------------

trivialExecutableCodeClosure :
  ∀ (Word : Set) →
  Exec.ExecutableCodeClosure Word
trivialExecutableCodeClosure Word = record
  { Exec.identityMapCode =
      trivialMapCode (λ word → word)
  ; Exec.precomposeDeciderCode =
      λ map decider mapCode deciderCode →
        trivialDeciderCode
          (λ word → decider (map word))
  }

------------------------------------------------------------------------
-- Therefore every base polynomial witness lifts to the generic executable
-- refinement.  The extra code field imposes no representation restriction.
------------------------------------------------------------------------

liftBasePolynomialMap :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {map : Word → Word} →
  PR.polynomialTimeMap base map →
  Exec.ExecutablePolynomialTimeMap base map
liftBasePolynomialMap polynomial =
  polynomial , trivialMapCode _

liftBasePolynomialDecider :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {decider : Word → Bool} →
  PR.polynomialTimeDecider base decider →
  Exec.ExecutablePolynomialTimeDecider base decider
liftBasePolynomialDecider polynomial =
  polynomial , trivialDeciderCode _

liftBasePolynomialVerifier :
  ∀ {Word Certificate : Set}
    {base : PR.PolynomialCostModel Word}
    {verifier : Word → Certificate → Bool} →
  PR.polynomialTimeVerifier base verifier →
  Exec.ExecutablePolynomialTimeVerifier base verifier
liftBasePolynomialVerifier polynomial =
  polynomial , trivialVerifierCode _

liftBaseInPToTrivialExecutableRefinement :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {language : PR.Language Word} →
  PR.InP base language →
  PR.InP
    (Exec.executablePolynomialCostModel
      base
      (trivialExecutableCodeClosure Word))
    language
liftBaseInPToTrivialExecutableRefinement baseP = record
  { PR.decide = PR.decide baseP
  ; PR.sound = PR.sound baseP
  ; PR.complete = PR.complete baseP
  ; PR.polynomialDecision =
      liftBasePolynomialDecider
        (PR.polynomialDecision baseP)
  }

------------------------------------------------------------------------
-- Exact boundary.
------------------------------------------------------------------------

record GenericExecutableRefinementBoundary : Set where
  constructor generic-executable-refinement-boundary
  field
    everyExtensionalMapHasSingletonCode : Bool
    everyExtensionalDeciderHasSingletonCode : Bool
    everyExtensionalVerifierHasSingletonCode : Bool
    everyBasePolynomialDeciderLifts : Bool
    finiteSerializableProgramForced : Bool
    concreteTapeExecutionForced : Bool

open import Agda.Builtin.Bool using (false; true)

canonicalGenericExecutableRefinementBoundary :
  GenericExecutableRefinementBoundary
canonicalGenericExecutableRefinementBoundary =
  generic-executable-refinement-boundary
    true true true true false false

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- `ExecutableDeciderCode` should be read as an execution-equation wrapper, not
-- yet as a finite program model.  The actual Clay-facing executable refinement
-- must additionally constrain code/interpreter representation, e.g. the
-- deterministic concrete-tape static bit program introduced on the max-cut
-- branch.
------------------------------------------------------------------------
