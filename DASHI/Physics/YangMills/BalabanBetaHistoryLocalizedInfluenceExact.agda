module DASHI.Physics.YangMills.BalabanBetaHistoryLocalizedInfluenceExact where

------------------------------------------------------------------------
-- ROUND82: LOCALIZED HISTORY INFLUENCE -> UNIFORM NONLINEAR BETA REMAINDER
--
-- PRIMARY SOURCE / MOTIVATION
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- At the end of Sect. 5 Bałaban explicitly notes that beta_j depends not only
-- on g_{j-1} but on all preceding effective couplings.  This is the reason a
-- pointwise one-loop calculation is not yet a history-uniform theorem.
-- The same paper proves exponential localization of the irrelevant remainder,
-- and CMP116/119 preserve localization under the later cluster resummations.
--
-- DASHI CONTRIBUTION
--
-- Do not bound the whole arbitrary-length coupling history by "number of past
-- scales times a local error".  Resolve the history response into shells whose
-- influence decays geometrically with distance from the current RG step.  The
-- already machine-checked geometric tail then gives a history-length-INDEPENDENT
-- remainder bound.
--
-- If
--
--   historyDifference_j <= sum_{d=0}^{j-1} influence_d,
--   influence_d <= C gamma (1/4) 2^{-d},
--
-- then for every j
--
--   historyDifference_j <= C gamma / 2.
--
-- Hence, if the zero-history constrained Gaussian coefficient is b>0 and
-- C gamma / 2 <= b/2, the full history-dependent coefficient remains >= b/2.
-- This isolates the real physical producer: a localized influence bound for the
-- literal Wilson/FP/Haar polarization coefficient.  It removes any dependence
-- on the number of preceding RG steps from the target estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

record LocalizedBetaHistoryInfluence : Set₁ where
  field
    coefficient gamma : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
    gammaNonnegative : 0ℚ ≤ gamma

    influenceMajorant : Scale.ScaleLocalIncrementMajorant
    majorantCoefficientExact :
      Scale.coefficient influenceMajorant ≡ coefficient * gamma

    historyDifference : Nat → Nat → ℚ
    historyDifferenceNonnegative : ∀ start count →
      0ℚ ≤ historyDifference start count
    historyDifferenceBelowInfluenceTail : ∀ start count →
      historyDifference start count
      ≤ Scale.scaleIncrementTail influenceMajorant start count

open LocalizedBetaHistoryInfluence public

historyDifferenceUniform :
  (dataSet : LocalizedBetaHistoryInfluence) → ∀ start count →
  historyDifference dataSet start count
  ≤ (coefficient dataSet * gamma dataSet)
      * (Geo.half * Geo.halfPower start)
historyDifferenceUniform dataSet start count =
  let
    tail = Scale.scaleLocalCauchyTail
      (influenceMajorant dataSet) start count
  in
  ℚP.≤-trans
    (historyDifferenceBelowInfluenceTail dataSet start count)
    (subst
      (λ c → Scale.scaleIncrementTail (influenceMajorant dataSet) start count
        ≤ c * (Geo.half * Geo.halfPower start))
      (majorantCoefficientExact dataSet)
      tail)

historyDifferenceFromPresentScale :
  (dataSet : LocalizedBetaHistoryInfluence) → ∀ count →
  historyDifference dataSet 0 count
  ≤ (coefficient dataSet * gamma dataSet) * Geo.half
historyDifferenceFromPresentScale dataSet count =
  subst
    (λ right → historyDifference dataSet 0 count ≤ right)
    (ℚRing.solve-∀
      (coefficient dataSet) (gamma dataSet) Geo.half
      (Geo.halfPower 0))
    (historyDifferenceUniform dataSet 0 count)

record PositiveGaussianAgainstHistory
    (history : LocalizedBetaHistoryInfluence) : Set₁ where
  field
    gaussianCoefficient : ℚ
    fullBeta : Nat → ℚ

    gaussianCoefficientNonnegative : 0ℚ ≤ gaussianCoefficient

    -- Division-free form of C gamma / 2 <= b / 2:
    historyBudgetFitsHalfGaussian :
      (coefficient history * gamma history) * Geo.half
      + gaussianCoefficient * Geo.half
      ≤ gaussianCoefficient

    betaAboveGaussianMinusHistory : ∀ count →
      gaussianCoefficient
      ≤ fullBeta count + historyDifference history 0 count

open PositiveGaussianAgainstHistory public

fullBetaKeepsHalfGaussian :
  ∀ {history}
    (dataSet : PositiveGaussianAgainstHistory history) count →
  gaussianCoefficient dataSet * Geo.half ≤ fullBeta dataSet count
fullBetaKeepsHalfGaussian {history} dataSet count =
  let
    h = historyDifference history 0 count
    hBound = historyDifferenceFromPresentScale history count
    budget = historyBudgetFitsHalfGaussian dataSet

    halfPlusHBelowGaussian :
      gaussianCoefficient dataSet * Geo.half + h
      ≤ gaussianCoefficient dataSet
    halfPlusHBelowGaussian =
      ℚP.≤-trans
        (ℚP.+-mono-≤ ℚP.≤-refl hBound)
        (subst
          (λ left → left ≤ gaussianCoefficient dataSet)
          (ℚRing.solve-∀
            (gaussianCoefficient dataSet)
            (coefficient history * gamma history)
            Geo.half)
          budget)

    chained :
      gaussianCoefficient dataSet * Geo.half + h
      ≤ fullBeta dataSet count + h
    chained = ℚP.≤-trans halfPlusHBelowGaussian
      (betaAboveGaussianMinusHistory dataSet count)
  in
  ℚP.+-cancelʳ-≤ h chained

localizedBetaHistoryInfluenceCompilerLevel : ProofLevel
localizedBetaHistoryInfluenceCompilerLevel = machineChecked

-- New physical target after this compiler: prove that changing a coupling d
-- scales back changes the literal polarization/beta coefficient by a summable
-- localized shell amount.  The bound must be uniform in cutoff, volume, scale,
-- compact-simple group package, and admissible preceding history.
literalBetaLocalizedHistoryInfluenceLevel : ProofLevel
literalBetaLocalizedHistoryInfluenceLevel = conditional
