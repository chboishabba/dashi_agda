module DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact where

------------------------------------------------------------------------
-- DIRECT SAT LOWER-BOUND RESEARCH SURFACE
--
-- This file is intentionally on the Clay-critical dependency path.
--
-- It does not add another complexity-class wrapper.  It states the concrete
-- theorem family that would close SATLowerBoundProducer on the repository's
-- existing PolynomialCostModel:
--
--   every polynomial-time Boolean SAT decider fails on some formula,
--
-- where failure means exactly one of:
--
--   * false positive: it returns true on an unsatisfiable formula;
--   * false negative: it returns false on a satisfiable formula.
--
-- The compiler below proves that an inhabitant of this universal failure
-- theorem yields SATNotInP and hence SATLowerBoundProducer immediately.
--
-- No inhabitant of UniversalPolynomialSATDecisionFailure is manufactured.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay

------------------------------------------------------------------------
-- Every candidate carries only the algorithm and the polynomial-time proof.
-- Correctness is deliberately NOT included: that is what the failure witness
-- is intended to refute.
------------------------------------------------------------------------

record PolynomialSATDeciderCandidate
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  constructor polynomial-sat-decider-candidate
  field
    decide : Cook.BooleanFormula → Bool
    polynomialDecision :
      PR.polynomialTimeDecider cost decide

open PolynomialSATDeciderCandidate public

inPToPolynomialSATDeciderCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InP cost Clay.SATLanguage →
  PolynomialSATDeciderCandidate cost
inPToPolynomialSATDeciderCandidate satP =
  polynomial-sat-decider-candidate
    (PR.decide satP)
    (PR.polynomialDecision satP)

------------------------------------------------------------------------
-- Concrete extensional failure modes.
------------------------------------------------------------------------

data SATDecisionFailure
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : PolynomialSATDeciderCandidate cost) : Set₁ where

  falsePositive :
    (formula : Cook.BooleanFormula) →
    decide candidate formula ≡ true →
    (Cook.Satisfiable formula → ⊥) →
    SATDecisionFailure candidate

  falseNegative :
    (formula : Cook.BooleanFormula) →
    Cook.Satisfiable formula →
    decide candidate formula ≡ false →
    SATDecisionFailure candidate

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- A correct SAT decider cannot possess either failure witness.
------------------------------------------------------------------------

failureContradictsCorrectSATDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage) →
  SATDecisionFailure (inPToPolynomialSATDeciderCandidate satP) →
  ⊥
failureContradictsCorrectSATDecision satP
    (falsePositive formula returnedTrue unsatisfiable) =
  unsatisfiable
    (PR.sound satP formula returnedTrue)

failureContradictsCorrectSATDecision satP
    (falseNegative formula satisfiable returnedFalse) =
  falseNotTrue
    (trans
      (sym returnedFalse)
      (PR.complete satP formula satisfiable))

------------------------------------------------------------------------
-- THE ACTUAL OPEN LOWER-BOUND THEOREM FAMILY.
--
-- This is the direct extensional form of the PDF's
--
--   forall polynomial-time M, exists phi,
--   M(phi) exceeds the claimed resource bound OR returns the wrong SAT value.
--
-- The resource excess alternative has already been absorbed into the
-- repository's PolynomialCostModel: only candidates certified by
-- polynomialTimeDecider are quantified here.  What remains is therefore the
-- unavoidable wrong-answer witness for every certified polynomial candidate.
------------------------------------------------------------------------

UniversalPolynomialSATDecisionFailure :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
UniversalPolynomialSATDecisionFailure cost =
  (candidate : PolynomialSATDeciderCandidate cost) →
  SATDecisionFailure candidate

------------------------------------------------------------------------
-- Clay-core compiler.
------------------------------------------------------------------------

universalDecisionFailureGivesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.SATNotInP cost
universalDecisionFailureGivesSATNotInP universalFailure satP =
  failureContradictsCorrectSATDecision
    satP
    (universalFailure
      (inPToPolynomialSATDeciderCandidate satP))

universalDecisionFailureGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.SATLowerBoundProducer cost
universalDecisionFailureGivesSATLowerBoundProducer universalFailure = record
  { Clay.satNotPolynomialTime =
      universalDecisionFailureGivesSATNotInP universalFailure
  }

universalDecisionFailureClosesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Clay.PNotEqualsNPEstablishedBackground cost →
  UniversalPolynomialSATDecisionFailure cost →
  Clay.PNotEqualsNP cost
universalDecisionFailureClosesPNotEqualsNP background universalFailure =
  Clay.satLowerBoundProducerClosesClayCore
    background
    (universalDecisionFailureGivesSATLowerBoundProducer universalFailure)

------------------------------------------------------------------------
-- Max-cut receipt.
--
-- The only novel theorem still missing in this file is an inhabitant of
-- UniversalPolynomialSATDecisionFailure for the standard cost model.
------------------------------------------------------------------------

record DirectSATLowerBoundResearchCut
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  field
    candidateCarrier :
      Set₁
    candidateCarrierIsPolynomialSATDeciders :
      candidateCarrier ≡ PolynomialSATDeciderCandidate cost
    failureType :
      PolynomialSATDeciderCandidate cost → Set₁
    failureTypeIsConcreteSATDecisionFailure :
      failureType ≡ SATDecisionFailure
    universalFailure :
      UniversalPolynomialSATDecisionFailure cost

open DirectSATLowerBoundResearchCut public

directResearchCutGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  DirectSATLowerBoundResearchCut cost →
  Clay.SATLowerBoundProducer cost
directResearchCutGivesSATLowerBoundProducer cut =
  universalDecisionFailureGivesSATLowerBoundProducer
    (universalFailure cut)
