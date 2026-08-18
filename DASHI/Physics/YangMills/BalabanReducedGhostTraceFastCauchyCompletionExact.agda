module DASHI.Physics.YangMills.BalabanReducedGhostTraceFastCauchyCompletionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", Dalhousie University,
-- 2022, arXiv:2205.08354. No DOI assigned.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity", LNCS 2277 (2002),
-- 79--95. DOI: 10.1007/3-540-45842-5_6.
--
-- DASHI CONTRIBUTION
--
-- Round61 already proves the SAME physical reduced-ghost matrix logarithm has
-- shifted row-tail cap
--
--     s_m = (1/5)^m / 2500
--
-- and s_m <= 2^{-m}.  Passing from a matrix row bound to an unnormalised trace
-- can cost at most the redundant coordinate count 3*256=768.  Crucially the
-- existing 1/2500 fifth-tail factor already absorbs that cost:
--
--     768 s_m <= 2^{-m}.
--
-- Therefore no extra loss of FastCauchy precision is needed at the trace level.
-- Once the actual finite trace-log partial sums satisfy the exact finite
-- difference estimate
--
--   |S_m-S_n| <= 768 s_m + 768 s_n,
--
-- this file constructs the repository's canonical FastCauchyReal immediately.
-- The remaining physical seam is narrowed to the SAME-object equality between
-- a partial-sum difference and the corresponding finite matrix tail; it is not
-- another convergence-rate theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; ∣_∣; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Fifth
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact as Shifted
import DASHI.Physics.YangMills.BalabanReducedGhostDyadicCauchyBudgetExact as Dyadic

traceCoordinateCap : ℚ
traceCoordinateCap = + 768 / 1

traceTimesFifthTailCap : ℚ
traceTimesFifthTailCap = traceCoordinateCap * Fifth.fifthTailCap

traceTimesFifthTailCapBelowOne : traceTimesFifthTailCap ≤ 1ℚ
traceTimesFifthTailCapBelowOne =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym
        (ℚRing.solve [] :
          1ℚ - traceTimesFifthTailCap ≡ (+ 433 / 625)))
      (ℚP.nonNegative⁻¹ (+ 433 / 625)))

traceAmplifiedShiftedCap : Nat → ℚ
traceAmplifiedShiftedCap start = traceCoordinateCap * Shifted.shiftedCap start

traceAmplifiedShiftedCapReassociate : ∀ start →
  traceAmplifiedShiftedCap start
  ≡ Shifted.startFactor start * traceTimesFifthTailCap
traceAmplifiedShiftedCapReassociate start = ℚRing.solve-∀

traceAmplifiedCapBelowStartFactor : ∀ start →
  traceAmplifiedShiftedCap start ≤ Shifted.startFactor start
traceAmplifiedCapBelowStartFactor start =
  let
    factor = Shifted.startFactor start

    instance
      factorNN : NonNegative factor
      factorNN = ℚ.nonNegative (Shifted.startFactorNonnegative start)

    scaled : factor * traceTimesFifthTailCap ≤ factor * 1ℚ
    scaled = ℚP.*-monoˡ-≤-nonNeg factor traceTimesFifthTailCapBelowOne
  in
  subst
    (λ lower → lower ≤ factor)
    (sym (traceAmplifiedShiftedCapReassociate start))
    (ℚP.≤-trans scaled (ℚP.≤-reflexive (ℚP.*-identityʳ factor)))

traceAmplifiedCapBelowDyadic : ∀ start →
  traceAmplifiedShiftedCap start ≤ Metric.dyadicQ start
traceAmplifiedCapBelowDyadic start =
  ℚP.≤-trans
    (traceAmplifiedCapBelowStartFactor start)
    (Dyadic.oneFifthPowerBelowDyadic start)

record ReducedGhostTracePartialSums : Set₁ where
  field
    partialTrace : Nat → ℚ

    -- This is the one remaining finite same-object statement required from the
    -- literal trace-log sequence.  It is deliberately stated before completion.
    pairwiseFiniteTailBound : ∀ m n →
      ∣ partialTrace m - partialTrace n ∣
      ≤ traceAmplifiedShiftedCap m + traceAmplifiedShiftedCap n

open ReducedGhostTracePartialSums public

partialTraceFastCauchy :
  (dataSet : ReducedGhostTracePartialSums) →
  ∀ m n →
  ∣ partialTrace dataSet m - partialTrace dataSet n ∣
  ≤ Metric.dyadicQ m + Metric.dyadicQ n
partialTraceFastCauchy dataSet m n =
  ℚP.≤-trans
    (pairwiseFiniteTailBound dataSet m n)
    (ℚP.+-mono-≤
      (traceAmplifiedCapBelowDyadic m)
      (traceAmplifiedCapBelowDyadic n))

reducedGhostTraceFastReal :
  ReducedGhostTracePartialSums →
  Fast.FastCauchyReal Metric.canonicalRationalMetricAuthority
reducedGhostTraceFastReal dataSet =
  Fast.fastReal
    (partialTrace dataSet)
    (partialTraceFastCauchy dataSet)

record ReducedGhostTraceFastCauchyBoundary : Set where
  field
    redundantTraceDimensionCostAbsorbed : Bool
    canonicalDyadicFastCauchyConstructed : Bool
    additionalConvergenceRateProducerRequired : Bool
    finiteTraceDifferenceSameObjectStillRequired : Bool
    principalLogDeterminantIdentificationStillRequired : Bool

canonicalReducedGhostTraceFastCauchyBoundary :
  ReducedGhostTraceFastCauchyBoundary
canonicalReducedGhostTraceFastCauchyBoundary = record
  { redundantTraceDimensionCostAbsorbed = true
  ; canonicalDyadicFastCauchyConstructed = true
  ; additionalConvergenceRateProducerRequired = false
  ; finiteTraceDifferenceSameObjectStillRequired = true
  ; principalLogDeterminantIdentificationStillRequired = true
  }

reducedGhostTraceDimensionAbsorptionLevel : ProofLevel
reducedGhostTraceDimensionAbsorptionLevel = machineChecked

reducedGhostTraceFastCauchyConstructionLevel : ProofLevel
reducedGhostTraceFastCauchyConstructionLevel = machineChecked

physicalTracePartialSumDifferenceTailIdentityLevel : ProofLevel
physicalTracePartialSumDifferenceTailIdentityLevel = conditional

principalMatrixLogReducedDeterminantSameObjectLevel : ProofLevel
principalMatrixLogReducedDeterminantSameObjectLevel = conditional
