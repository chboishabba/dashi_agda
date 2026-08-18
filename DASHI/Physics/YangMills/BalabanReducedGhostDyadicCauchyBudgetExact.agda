module DASHI.Physics.YangMills.BalabanReducedGhostDyadicCauchyBudgetExact where

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
-- The reduced-ghost branch now has an explicit geometric late-tail modulus
--
--       rowMass(Tail_m) <= (1/5)^m / 2500.
--
-- DASHI's canonical FastCauchy rational metric uses the dyadic error
--
--       epsilon_m = (1/2)^m.
--
-- This module proves internally that the physical ghost modulus is strictly
-- faster than the canonical dyadic one:
--
--       (1/5)^m <= (1/2)^m,
--       (1/5)^m / 2500 <= (1/2)^m.
--
-- Hence every shifted finite matrix-log tail already satisfies the numerical
-- error schedule required by the repo's FastCauchy/Bishop completion stack.
-- The remaining completion seam is representational: choose/identify the
-- actual matrix-log partial-sum sequence and transport it through the existing
-- constructive completion.  No stronger analytic decay estimate is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; ½; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Fifth
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogShiftedTailExact as Shifted

oneFifthBelowHalf : Fifth.oneFifth ≤ ½
oneFifthBelowHalf = ℚP.<⇒≤ (ℚP.positiveDifference⇒< (ℚP.nonNegative⁻¹ (+ 3 / 10)))

-- Both powers use the same left-recursive multiplication convention.
oneFifthPowerBelowDyadic : ∀ exponent →
  Neumann.rationalPower Fifth.oneFifth exponent ≤ Metric.dyadicQ exponent
oneFifthPowerBelowDyadic zero = ℚP.≤-refl
oneFifthPowerBelowDyadic (suc exponent) =
  let
    fifthPower = Neumann.rationalPower Fifth.oneFifth exponent
    dyadicPower = Metric.dyadicQ exponent

    instance
      fifthPowerNN : NonNegative fifthPower
      fifthPowerNN = ℚ.nonNegative
        (Neumann.powerNonnegative
          Fifth.oneFifth exponent Fifth.oneFifthNonnegative)
      halfNN : NonNegative ½
      halfNN = ℚ.nonNegative Metric.halfNonnegative

    first : Fifth.oneFifth * fifthPower ≤ ½ * fifthPower
    first = ℚP.*-monoʳ-≤-nonNeg fifthPower oneFifthBelowHalf

    second : ½ * fifthPower ≤ ½ * dyadicPower
    second = ℚP.*-monoˡ-≤-nonNeg ½
      (oneFifthPowerBelowDyadic exponent)
  in
  ℚP.≤-trans first second

fifthTailCapBelowOne : Fifth.fifthTailCap ≤ 1ℚ
fifthTailCapBelowOne =
  ℚP.<⇒≤ (ℚP.positiveDifference⇒< (ℚP.nonNegative⁻¹ (+ 2499 / 2500)))

shiftedCapBelowStartFactor : ∀ start →
  Shifted.shiftedCap start ≤ Shifted.startFactor start
shiftedCapBelowStartFactor start =
  let
    factor = Shifted.startFactor start
    instance
      factorNN : NonNegative factor
      factorNN = ℚ.nonNegative (Shifted.startFactorNonnegative start)
  in
  ℚP.≤-trans
    (ℚP.*-monoˡ-≤-nonNeg factor fifthTailCapBelowOne)
    (ℚP.≤-reflexive (ℚP.*-identityʳ factor))

shiftedCapBelowDyadic : ∀ start →
  Shifted.shiftedCap start ≤ Metric.dyadicQ start
shiftedCapBelowDyadic start =
  ℚP.≤-trans
    (shiftedCapBelowStartFactor start)
    (oneFifthPowerBelowDyadic start)

------------------------------------------------------------------------
-- Generic row-budget adapter: any late finite tail carrying the stronger
-- shifted cap automatically carries the canonical dyadic FastCauchy budget.
------------------------------------------------------------------------

dyadicRowBudgetFromShiftedCap :
  ∀ value start →
  value ≤ Shifted.shiftedCap start →
  value ≤ Metric.dyadicQ start
dyadicRowBudgetFromShiftedCap value start below =
  ℚP.≤-trans below (shiftedCapBelowDyadic start)

reducedGhostOneFifthBeatsDyadicLevel : ProofLevel
reducedGhostOneFifthBeatsDyadicLevel = machineChecked

reducedGhostShiftedTailFitsCanonicalFastCauchyBudgetLevel : ProofLevel
reducedGhostShiftedTailFitsCanonicalFastCauchyBudgetLevel = machineChecked

-- The unresolved theorem is no longer a rate comparison.  It is the actual
-- sequence realization / principal-log identification in the complete
-- constructive-real matrix carrier.
physicalReducedGhostFastCauchySequenceRealizationLevel : ProofLevel
physicalReducedGhostFastCauchySequenceRealizationLevel = conditional
