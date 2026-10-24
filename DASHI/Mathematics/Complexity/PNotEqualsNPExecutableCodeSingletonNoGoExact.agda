module DASHI.Mathematics.Complexity.PNotEqualsNPExecutableCodeSingletonNoGoExact where

------------------------------------------------------------------------
-- GENERIC EXECUTABLE-CODE REFINEMENT STILL DOES NOT FORCE QUOTABLE PROGRAMS
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as Exec

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

liftBasePolynomialMap :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {map : Word → Word} →
  PR.polynomialTimeMap base map →
  Exec.ExecutablePolynomialTimeMap base map
liftBasePolynomialMap {map = map} polynomial =
  polynomial , trivialMapCode map

liftBasePolynomialDecider :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {decider : Word → Bool} →
  PR.polynomialTimeDecider base decider →
  Exec.ExecutablePolynomialTimeDecider base decider
liftBasePolynomialDecider {decider = decider} polynomial =
  polynomial , trivialDeciderCode decider

liftBasePolynomialVerifier :
  ∀ {Word Certificate : Set}
    {base : PR.PolynomialCostModel Word}
    {verifier : Word → Certificate → Bool} →
  PR.polynomialTimeVerifier base verifier →
  Exec.ExecutablePolynomialTimeVerifier base verifier
liftBasePolynomialVerifier {verifier = verifier} polynomial =
  polynomial , trivialVerifierCode verifier

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

record GenericExecutableRefinementBoundary : Set where
  constructor generic-executable-refinement-boundary
  field
    everyExtensionalMapHasSingletonCode : Bool
    everyExtensionalDeciderHasSingletonCode : Bool
    everyExtensionalVerifierHasSingletonCode : Bool
    everyBasePolynomialDeciderLifts : Bool
    finiteSerializableProgramForced : Bool
    concreteTapeExecutionForced : Bool

canonicalGenericExecutableRefinementBoundary :
  GenericExecutableRefinementBoundary
canonicalGenericExecutableRefinementBoundary =
  generic-executable-refinement-boundary
    true true true true false false

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- ExecutableDeciderCode is an execution-equation wrapper, not yet a finite
-- serializable program model.  The literal deterministic concrete-tape code is
-- a genuinely stronger representation surface.
------------------------------------------------------------------------
