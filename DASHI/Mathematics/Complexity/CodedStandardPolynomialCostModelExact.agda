module DASHI.Mathematics.Complexity.CodedStandardPolynomialCostModelExact where

------------------------------------------------------------------------
-- CONCRETE STANDARD-MACHINE POLYNOMIAL COST MODEL
--
-- The old PolynomialCostModel is intentionally parametric.  Rather than try to
-- extract finite programs from an arbitrary predicate, instantiate a model in
-- which polynomial decider evidence IS the Set-level coded standard-machine
-- witness constructed in CodedStandardPolynomialDeciderExact.
--
-- Only the generic closure infrastructure remains parameterized here:
--   * polynomial maps;
--   * map -> coded-decider precomposition compiler;
--   * polynomial verifiers;
--   * certificate bounds.
--
-- For this model, SAT-candidate standard-machine coverage follows by projection,
-- not by an additional representation axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedStandardPolynomialDeciderExact as CodedDecider
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedStandardCandidateBridgeExact as CandidateBridge
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardMachineMaxCutClosureExact as Closure

------------------------------------------------------------------------
-- Auxiliary closure data not specific to SAT.
------------------------------------------------------------------------

record CodedStandardCostClosure : Set₂ where
  field
    polynomialTimeMap :
      (Cook.BooleanFormula → Cook.BooleanFormula) → Set

    polynomialTimeVerifier :
      ∀ {Certificate : Set} →
      (Cook.BooleanFormula → Certificate → Bool) → Set

    polynomialCertificateBound :
      ∀ {Certificate : Set} →
      (Cook.BooleanFormula → Certificate → Set) → Set

    identityMapPolynomial :
      polynomialTimeMap (λ formula → formula)

    precomposeCodedDecider :
      (map : Cook.BooleanFormula → Cook.BooleanFormula) →
      (decider : Cook.BooleanFormula → Bool) →
      polynomialTimeMap map →
      CodedDecider.CodedStandardPolynomialDecider decider →
      CodedDecider.CodedStandardPolynomialDecider
        (λ formula → decider (map formula))

open CodedStandardCostClosure public

------------------------------------------------------------------------
-- Literal PolynomialCostModel instance.
------------------------------------------------------------------------

codedStandardPolynomialCostModel :
  CodedStandardCostClosure →
  PR.PolynomialCostModel Cook.BooleanFormula
codedStandardPolynomialCostModel closure = record
  { PR.polynomialTimeMap =
      polynomialTimeMap closure
  ; PR.polynomialTimeDecider =
      CodedDecider.CodedStandardPolynomialDecider
  ; PR.polynomialTimeVerifier =
      polynomialTimeVerifier closure
  ; PR.polynomialCertificateBound =
      polynomialCertificateBound closure
  ; PR.identityMapPolynomial =
      identityMapPolynomial closure
  ; PR.deciderClosedUnderPrecomposition =
      precomposeCodedDecider closure
  }

------------------------------------------------------------------------
-- A is automatic for candidates certified polynomial in this concrete model.
------------------------------------------------------------------------

codedStandardCostCandidateCoverage :
  (closure : CodedStandardCostClosure) →
  Closure.StandardPolynomialCandidateCoverage
    (codedStandardPolynomialCostModel closure)
codedStandardCostCandidateCoverage closure = record
  { Closure.realize =
      λ candidate →
        CandidateBridge.codedWitnessToPolynomiallyClockedCandidate
          (Direct.polynomialDecision candidate)
  }

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- MODEL IDENTIFICATION has now split cleanly:
--
--   * inside this concrete standard-machine cost model, candidate coverage A is
--     definitionally/projectionally paid;
--   * relating some OTHER abstract PolynomialCostModel to this one is a model-
--     equivalence theorem and must not be assumed parametrically.
--
-- Remaining generic cost engineering is exactly the closure record above.  It
-- is ordinary complexity-model infrastructure, separate from the SAT diagonal.
------------------------------------------------------------------------
