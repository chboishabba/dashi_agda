module DASHI.Physics.YangMills.BalabanStrongCouplingSUFourDimensionalMarginExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- SOURCE FORMULA
--
-- For SU(N), Shen--Zhu--Zhu obtain the Bakry--Emery constant
--
--   K_S = (N+2)/2 - 1 - 8 N |beta| (d-1)
--       = N (1/2 - 8 |beta| (d-1)).
--
-- Their Hessian estimate splits into the diagonal and off-diagonal costs
--
--   2 N |beta| (d-1) + 6 N |beta| (d-1)
--     = 8 N |beta| (d-1).
--
-- In d=4 this becomes
--
--   K_S = N (1/2 - 24 |beta|),
--
-- so positivity is equivalent to |beta| < 1/48.
--
-- DASHI CONTRIBUTION
--
-- Normalize the complete coefficient arithmetic over exact rationals, expose
-- the diagonal/cross incidence split 6+18=24 in four dimensions, factor the
-- curvature margin by the exact threshold slack, and check one strict interior
-- point |beta|=1/96.  This is finite algebra from the published proof; it does
-- not formalize the manifold Hessian bound, Bakry--Emery theorem, Langevin SDE,
-- infinite-volume limit, or spatial correlation argument.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _/_; _<_; Positive)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

fourDimensionalDMinusOne : ℚ
fourDimensionalDMinusOne = + 3 / 1

suRicciPerRank : ℚ
suRicciPerRank = + 1 / 2

paperDiagonalHessianCostPerRank : ℚ → ℚ
paperDiagonalHessianCostPerRank betaMagnitude =
  (+ 2 / 1) * fourDimensionalDMinusOne * betaMagnitude

paperCrossHessianCostPerRank : ℚ → ℚ
paperCrossHessianCostPerRank betaMagnitude =
  (+ 6 / 1) * fourDimensionalDMinusOne * betaMagnitude

paperTotalHessianCostPerRank : ℚ → ℚ
paperTotalHessianCostPerRank betaMagnitude =
  (+ 8 / 1) * fourDimensionalDMinusOne * betaMagnitude

fourDimensionalDiagonalCoefficientExact :
  ∀ betaMagnitude →
  paperDiagonalHessianCostPerRank betaMagnitude
  ≡ (+ 6 / 1) * betaMagnitude
fourDimensionalDiagonalCoefficientExact betaMagnitude =
  solve (betaMagnitude ∷ [])

fourDimensionalCrossCoefficientExact :
  ∀ betaMagnitude →
  paperCrossHessianCostPerRank betaMagnitude
  ≡ (+ 18 / 1) * betaMagnitude
fourDimensionalCrossCoefficientExact betaMagnitude =
  solve (betaMagnitude ∷ [])

fourDimensionalTotalCoefficientExact :
  ∀ betaMagnitude →
  paperTotalHessianCostPerRank betaMagnitude
  ≡ (+ 24 / 1) * betaMagnitude
fourDimensionalTotalCoefficientExact betaMagnitude =
  solve (betaMagnitude ∷ [])

diagonalPlusCrossIsTotal :
  ∀ betaMagnitude →
  paperDiagonalHessianCostPerRank betaMagnitude
    + paperCrossHessianCostPerRank betaMagnitude
  ≡ paperTotalHessianCostPerRank betaMagnitude
diagonalPlusCrossIsTotal betaMagnitude =
  solve (betaMagnitude ∷ [])

suNormalizedBakryEmeryMargin : ℚ → ℚ
suNormalizedBakryEmeryMargin betaMagnitude =
  suRicciPerRank - paperTotalHessianCostPerRank betaMagnitude

suFourDimensionalStrongCouplingThreshold : ℚ
suFourDimensionalStrongCouplingThreshold = + 1 / 48

thresholdSaturatesMargin :
  suNormalizedBakryEmeryMargin suFourDimensionalStrongCouplingThreshold
  ≡ 0ℚ
thresholdSaturatesMargin = solve []

marginFactorsThroughThresholdSlack :
  ∀ betaMagnitude →
  suNormalizedBakryEmeryMargin betaMagnitude
  ≡ (+ 24 / 1)
      * (suFourDimensionalStrongCouplingThreshold - betaMagnitude)
marginFactorsThroughThresholdSlack betaMagnitude =
  solve (betaMagnitude ∷ [])

paperSUCurvatureConstant : ℚ → ℚ → ℚ
paperSUCurvatureConstant rankN betaMagnitude =
  rankN * suNormalizedBakryEmeryMargin betaMagnitude

paperSUCurvatureConstantExpanded :
  ∀ rankN betaMagnitude →
  paperSUCurvatureConstant rankN betaMagnitude
  ≡ rankN * ((+ 1 / 2) - (+ 24 / 1) * betaMagnitude)
paperSUCurvatureConstantExpanded rankN betaMagnitude =
  solve (rankN ∷ betaMagnitude ∷ [])

configuredInteriorBeta : ℚ
configuredInteriorBeta = + 1 / 96

configuredThresholdSlack : ℚ
configuredThresholdSlack =
  suFourDimensionalStrongCouplingThreshold - configuredInteriorBeta

configuredThresholdSlackExact :
  configuredThresholdSlack ≡ + 1 / 96
configuredThresholdSlackExact = solve []

configuredNormalizedMarginExact :
  suNormalizedBakryEmeryMargin configuredInteriorBeta ≡ + 1 / 4
configuredNormalizedMarginExact = solve []

configuredNormalizedMarginPositive :
  0ℚ < suNormalizedBakryEmeryMargin configuredInteriorBeta
configuredNormalizedMarginPositive =
  let
    instance
      quarterPositive : Positive (+ 1 / 4)
      quarterPositive = ℚP.normalize-pos 1 4
  in
  subst
    (λ selected → 0ℚ < selected)
    (sym configuredNormalizedMarginExact)
    (ℚP.positive⁻¹ (+ 1 / 4))

configuredSU2CurvatureConstantExact :
  paperSUCurvatureConstant (+ 2 / 1) configuredInteriorBeta
  ≡ + 1 / 2
configuredSU2CurvatureConstantExact = solve []
