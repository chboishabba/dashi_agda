module DASHI.Mathematics.Complexity.CodedStandardPolynomialCostModelExact where

------------------------------------------------------------------------
-- CONCRETE STANDARD-MACHINE POLYNOMIAL COST MODEL
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
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
  { PR.polynomialTimeMap = polynomialTimeMap closure
  ; PR.polynomialTimeDecider = CodedDecider.CodedStandardPolynomialDecider
  ; PR.polynomialTimeVerifier = polynomialTimeVerifier closure
  ; PR.polynomialCertificateBound = polynomialCertificateBound closure
  ; PR.identityMapPolynomial = identityMapPolynomial closure
  ; PR.deciderClosedUnderPrecomposition = precomposeCodedDecider closure
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
-- Therefore, in this concrete model, only the resource-closing compiler remains
-- on the SAT lower-bound path.
------------------------------------------------------------------------

codedStandardResourceCompilerGivesSATNotInP :
  (closure : CodedStandardCostClosure) →
  Closure.ResourceClosingCompiler
    (codedStandardCostCandidateCoverage closure) →
  Clay.SATNotInP (codedStandardPolynomialCostModel closure)
codedStandardResourceCompilerGivesSATNotInP closure compiler =
  Closure.standardMaxCutGivesSATNotInP
    (codedStandardCostCandidateCoverage closure)
    compiler

codedStandardResourceCompilerGivesPNotEqualsNP :
  (closure : CodedStandardCostClosure) →
  Clay.PNotEqualsNPEstablishedBackground
    (codedStandardPolynomialCostModel closure) →
  Closure.ResourceClosingCompiler
    (codedStandardCostCandidateCoverage closure) →
  Clay.PNotEqualsNP (codedStandardPolynomialCostModel closure)
codedStandardResourceCompilerGivesPNotEqualsNP
    closure background compiler =
  Closure.standardMaxCutGivesPNotEqualsNP
    background
    (codedStandardCostCandidateCoverage closure)
    compiler

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Inside this concrete standard-machine model, candidate coverage A is paid by
-- projection. The Clay-critical residual is therefore the resource-closing
-- compiler B, plus ordinary model infrastructure/background for this same cost
-- model (maps/precomposition, verifiers/certificates, SAT-in-NP/NP-completeness).
--
-- Relating some OTHER abstract PolynomialCostModel to this one remains a
-- separate model-equivalence theorem and is never assumed parametrically.
------------------------------------------------------------------------
