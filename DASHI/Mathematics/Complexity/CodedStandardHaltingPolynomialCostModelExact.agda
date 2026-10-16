module DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialCostModelExact where

------------------------------------------------------------------------
-- COOK-READY ACTUAL-HALTING STANDARD-MACHINE COST MODEL
--
-- This supersedes the padded-budget coded model on the Clay-critical path.
-- `polynomialTimeDecider` now means:
--   actual quiescent standard execution from canonical input
--   + polynomial upper bound
--   + guarded-representation transport at that SAME actual runtime.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardMachineMaxCutClosureExact as Closure

record CookReadyHaltingPolynomialDecider
    (decider : Cook.BooleanFormula → Bool) : Set where
  field
    halting : Halting.CodedStandardHaltingPolynomialDecider decider
    guarded : Halting.GuardedExecutionReceipt halting

open CookReadyHaltingPolynomialDecider public

record HaltingStandardCostClosure : Set₂ where
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

    precomposeHaltingDecider :
      (map : Cook.BooleanFormula → Cook.BooleanFormula) →
      (decider : Cook.BooleanFormula → Bool) →
      polynomialTimeMap map →
      CookReadyHaltingPolynomialDecider decider →
      CookReadyHaltingPolynomialDecider
        (λ formula → decider (map formula))

open HaltingStandardCostClosure public

haltingStandardPolynomialCostModel :
  HaltingStandardCostClosure →
  PR.PolynomialCostModel Cook.BooleanFormula
haltingStandardPolynomialCostModel closure = record
  { PR.polynomialTimeMap = polynomialTimeMap closure
  ; PR.polynomialTimeDecider = CookReadyHaltingPolynomialDecider
  ; PR.polynomialTimeVerifier = polynomialTimeVerifier closure
  ; PR.polynomialCertificateBound = polynomialCertificateBound closure
  ; PR.identityMapPolynomial = identityMapPolynomial closure
  ; PR.deciderClosedUnderPrecomposition = precomposeHaltingDecider closure
  }

haltingCostCandidateCoverage :
  (closure : HaltingStandardCostClosure) →
  Closure.StandardPolynomialCandidateCoverage
    (haltingStandardPolynomialCostModel closure)
haltingCostCandidateCoverage closure = record
  { Closure.realize = λ candidate →
      Bridge.haltingWitnessToPolynomiallyClockedCandidate
        (halting (Direct.polynomialDecision candidate))
        (guarded (Direct.polynomialDecision candidate))
  }

haltingResourceCompilerGivesSATNotInP :
  (closure : HaltingStandardCostClosure) →
  Closure.ResourceClosingCompiler
    (haltingCostCandidateCoverage closure) →
  Clay.SATNotInP (haltingStandardPolynomialCostModel closure)
haltingResourceCompilerGivesSATNotInP closure compiler =
  Closure.standardMaxCutGivesSATNotInP
    (haltingCostCandidateCoverage closure)
    compiler

haltingResourceCompilerGivesPNotEqualsNP :
  (closure : HaltingStandardCostClosure) →
  Clay.PNotEqualsNPEstablishedBackground
    (haltingStandardPolynomialCostModel closure) →
  Closure.ResourceClosingCompiler
    (haltingCostCandidateCoverage closure) →
  Clay.PNotEqualsNP (haltingStandardPolynomialCostModel closure)
haltingResourceCompilerGivesPNotEqualsNP closure background compiler =
  Closure.standardMaxCutGivesPNotEqualsNP
    background
    (haltingCostCandidateCoverage closure)
    compiler

------------------------------------------------------------------------
-- MODEL-IDENTIFICATION FIREWALL
--
-- This concrete model is now operationally faithful about runtime.  Equality
-- with a textbook standard-TM P model still requires the ordinary theorem that
-- canonical minimal-input executions transport to/from sufficiently blank-padded
-- guarded representations without changing decision or actual halting time.
-- That theorem is representation infrastructure, not SAT hardness, and remains
-- explicit until proved.
------------------------------------------------------------------------
