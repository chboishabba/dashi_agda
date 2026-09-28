module DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact where

------------------------------------------------------------------------
-- EXECUTABLE REFINEMENT OF AN EXTENSIONAL POLYNOMIAL COST MODEL
--
-- PolynomialCostModel is intentionally extensional:
--
--   polynomialTimeDecider : (Word -> Bool) -> Set
--
-- so an arbitrary witness does not carry program syntax.
--
-- Rather than postulate code extraction from that abstract predicate, this
-- module defines a REFINEMENT in which executable realization is part of the
-- polynomial witness by construction.  Forgetting the executable component
-- recovers the original cost model.
--
-- This is representation/model plumbing.  It is not a P != NP theorem and
-- does not assert that every abstract polynomial witness admits code.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual

------------------------------------------------------------------------
-- Executable finite-description surfaces.
--
-- Code is an explicit carrier with an exact interpreter equation and a size.
-- A later concrete tape/universal-machine instantiation may choose Code to be
-- the repository's literal static program bits.
------------------------------------------------------------------------

record ExecutableMapCode
    {Word : Set}
    (map : Word → Word) : Set₁ where
  field
    Code : Set
    code : Code
    run : Code → Word → Word
    runExact : (word : Word) → run code word ≡ map word
    codeSize : Code → Nat

open ExecutableMapCode public

record ExecutableDeciderCode
    {Word : Set}
    (decider : Word → Bool) : Set₁ where
  field
    Code : Set
    code : Code
    run : Code → Word → Bool
    runExact : (word : Word) → run code word ≡ decider word
    codeSize : Code → Nat

open ExecutableDeciderCode public

record ExecutableVerifierCode
    {Word Certificate : Set}
    (verifier : Word → Certificate → Bool) : Set₁ where
  field
    Code : Set
    code : Code
    run : Code → Word → Certificate → Bool
    runExact :
      (word : Word) →
      (certificate : Certificate) →
      run code word certificate ≡ verifier word certificate
    codeSize : Code → Nat

open ExecutableVerifierCode public

------------------------------------------------------------------------
-- Code constructors needed by PolynomialCostModel's two built-in closure laws.
------------------------------------------------------------------------

record ExecutableCodeClosure (Word : Set) : Set₂ where
  field
    identityMapCode :
      ExecutableMapCode (λ word → word)

    precomposeDeciderCode :
      (map : Word → Word) →
      (decider : Word → Bool) →
      ExecutableMapCode map →
      ExecutableDeciderCode decider →
      ExecutableDeciderCode
        (λ word → decider (map word))

open ExecutableCodeClosure public

------------------------------------------------------------------------
-- Refined predicates.
------------------------------------------------------------------------

ExecutablePolynomialTimeMap :
  ∀ {Word : Set} →
  PR.PolynomialCostModel Word →
  (Word → Word) →
  Set₁
ExecutablePolynomialTimeMap base map =
  PR.polynomialTimeMap base map
  × ExecutableMapCode map

ExecutablePolynomialTimeDecider :
  ∀ {Word : Set} →
  PR.PolynomialCostModel Word →
  (Word → Bool) →
  Set₁
ExecutablePolynomialTimeDecider base decider =
  PR.polynomialTimeDecider base decider
  × ExecutableDeciderCode decider

ExecutablePolynomialTimeVerifier :
  ∀ {Word Certificate : Set} →
  PR.PolynomialCostModel Word →
  (Word → Certificate → Bool) →
  Set₁
ExecutablePolynomialTimeVerifier base verifier =
  PR.polynomialTimeVerifier base verifier
  × ExecutableVerifierCode verifier

------------------------------------------------------------------------
-- Literal refined PolynomialCostModel.
--
-- Maps, deciders and verifiers retain the old polynomial witness AND acquire
-- executable code.  Certificate bounds are inherited unchanged because they
-- are size predicates rather than executable Boolean procedures.
------------------------------------------------------------------------

executablePolynomialCostModel :
  ∀ {Word : Set} →
  (base : PR.PolynomialCostModel Word) →
  ExecutableCodeClosure Word →
  PR.PolynomialCostModel Word
executablePolynomialCostModel base closure = record
  { PR.polynomialTimeMap =
      ExecutablePolynomialTimeMap base
  ; PR.polynomialTimeDecider =
      ExecutablePolynomialTimeDecider base
  ; PR.polynomialTimeVerifier =
      ExecutablePolynomialTimeVerifier base
  ; PR.polynomialCertificateBound =
      PR.polynomialCertificateBound base
  ; PR.identityMapPolynomial =
      PR.identityMapPolynomial base
      ,
      ExecutableCodeClosure.identityMapCode closure
  ; PR.deciderClosedUnderPrecomposition =
      closeDecider
  }
  where
    closeDecider :
      (map : Word → Word) →
      (decider : Word → Bool) →
      ExecutablePolynomialTimeMap base map →
      ExecutablePolynomialTimeDecider base decider →
      ExecutablePolynomialTimeDecider base
        (λ word → decider (map word))
    closeDecider
        map
        decider
        (mapPolynomial , mapCode)
        (deciderPolynomial , deciderCode) =
      PR.deciderClosedUnderPrecomposition
        base
        map
        decider
        mapPolynomial
        deciderPolynomial
      ,
      ExecutableCodeClosure.precomposeDeciderCode
        closure
        map
        decider
        mapCode
        deciderCode

------------------------------------------------------------------------
-- Forgetful direction: refined polynomial witnesses are ordinary base-model
-- polynomial witnesses.  No converse is asserted.
------------------------------------------------------------------------

forgetExecutableMap :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {map : Word → Word} →
  ExecutablePolynomialTimeMap base map →
  PR.polynomialTimeMap base map
forgetExecutableMap =
  proj₁

forgetExecutableDecider :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {decider : Word → Bool} →
  ExecutablePolynomialTimeDecider base decider →
  PR.polynomialTimeDecider base decider
forgetExecutableDecider =
  proj₁

forgetExecutableVerifier :
  ∀ {Word Certificate : Set}
    {base : PR.PolynomialCostModel Word}
    {verifier : Word → Certificate → Bool} →
  ExecutablePolynomialTimeVerifier base verifier →
  PR.polynomialTimeVerifier base verifier
forgetExecutableVerifier =
  proj₁

executableDeciderCode :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {decider : Word → Bool} →
  ExecutablePolynomialTimeDecider base decider →
  ExecutableDeciderCode decider
executableDeciderCode =
  proj₂

------------------------------------------------------------------------
-- InP forgetful compiler.
------------------------------------------------------------------------

forgetExecutableInP :
  ∀ {Word : Set}
    {base : PR.PolynomialCostModel Word}
    {closure : ExecutableCodeClosure Word}
    {language : PR.Language Word} →
  PR.InP
    (executablePolynomialCostModel base closure)
    language →
  PR.InP base language
forgetExecutableInP executableP = record
  { PR.decide =
      PR.decide executableP
  ; PR.sound =
      PR.sound executableP
  ; PR.complete =
      PR.complete executableP
  ; PR.polynomialDecision =
      forgetExecutableDecider
        (PR.polynomialDecision executableP)
  }

------------------------------------------------------------------------
-- SAT specialization: executable polynomial evidence projects directly to the
-- same-object CandidateCodeRealization expected by the self-instantiation lane.
------------------------------------------------------------------------

candidateCodeRealizationFromExecutableWitness :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool}
    (witness :
      ExecutablePolynomialTimeDecider
        base
        decider) →
  let refined =
        executablePolynomialCostModel base closure
      candidate =
        Direct.polynomial-sat-decider-candidate
          decider
          witness
  in
  Actual.CandidateCodeRealization candidate
candidateCodeRealizationFromExecutableWitness
    witness =
  record
    { Actual.CandidateCode =
        ExecutableDeciderCode.Code
          (executableDeciderCode witness)
    ; Actual.candidateCode =
        ExecutableDeciderCode.code
          (executableDeciderCode witness)
    ; Actual.runCandidateCode =
        ExecutableDeciderCode.run
          (executableDeciderCode witness)
    ; Actual.codeDecisionExact =
        ExecutableDeciderCode.runExact
          (executableDeciderCode witness)
    ; Actual.codeSize =
        ExecutableDeciderCode.codeSize
          (executableDeciderCode witness)
    }

satInExecutablePProvidesCandidateCode :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecutableCodeClosure Cook.BooleanFormula}
    {language : PR.Language Cook.BooleanFormula}
    (satP :
      PR.InP
        (executablePolynomialCostModel base closure)
        language) →
  Actual.CandidateCodeRealization
    (Direct.inPToPolynomialSATDeciderCandidate satP)
satInExecutablePProvidesCandidateCode satP =
  candidateCodeRealizationFromExecutableWitness
    (PR.polynomialDecision satP)

------------------------------------------------------------------------
-- Boundary statement.
------------------------------------------------------------------------

data ExecutableCostRefinementStatus : Set where
  executableWitnessIncludedByConstruction : ExecutableCostRefinementStatus
  forgetfulDirectionToExtensionalModelPaid : ExecutableCostRefinementStatus
  arbitraryExtensionalWitnessCodeExtractionPaid : ExecutableCostRefinementStatus
  concreteTapeUniversalInterpreterPaid : ExecutableCostRefinementStatus

currentExecutableCostRefinementStatus :
  ExecutableCostRefinementStatus
currentExecutableCostRefinementStatus =
  forgetfulDirectionToExtensionalModelPaid

------------------------------------------------------------------------
-- FRONTIER
--
-- This fixes the TYPE of A0 without narrowing it silently:
--
--   choose/justify a standard executable refinement model
--      ->
--   every SAT-in-P witness in THAT model carries executable code by projection.
--
-- What remains before calling the model "the repository's standard concrete
-- machine model" is a concrete finite-machine instantiation of
-- ExecutableCodeClosure plus the corresponding map/verifier machinery.
--
-- No theorem extracts code from arbitrary witnesses of the old extensional
-- PolynomialCostModel.
------------------------------------------------------------------------
