module DASHI.Physics.YangMills.BalabanStrongCouplingSUFormulaReconciliationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- Assumption 1.1 states separately
--
--   C_Ric,N(SO(N)) = (N+2)/4 - 1,
--   C_Ric,N(SU(N)) = (N+2)/2 - 1.
--
-- The second expression is exactly N/2.  This module proves that the earlier
-- SU-only Round-30 normalization and the new group-indexed primary-source
-- normalization are identical, including the d=4 threshold and configured
-- SU(2), |beta|=1/96 regression.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanStrongCouplingSUFourDimensionalMarginExact as Old
import DASHI.Physics.YangMills.BalabanStrongCouplingGroupRicciConstantsExact as Group

suRicciConstantMatchesOldPerRank :
  ∀ rankN →
  Group.ricciConstant Group.specialUnitaryFamily rankN
  ≡ rankN * Old.suRicciPerRank
suRicciConstantMatchesOldPerRank rankN = solve (rankN ∷ [])

suFourDimensionalRateMatchesOldNormalization :
  ∀ rankN betaMagnitude →
  Group.specialUnitaryFourDimensionalRate rankN betaMagnitude
  ≡ rankN * Old.suNormalizedBakryEmeryMargin betaMagnitude
suFourDimensionalRateMatchesOldNormalization rankN betaMagnitude =
  solve (rankN ∷ betaMagnitude ∷ [])

suThresholdMatchesOldThreshold :
  Group.specialUnitaryThreshold
  ≡ Old.suFourDimensionalStrongCouplingThreshold
suThresholdMatchesOldThreshold = solve []

configuredSU2RateMatchesOld :
  Group.specialUnitaryFourDimensionalRate
    (+ 2 / 1) Old.configuredInteriorBeta
  ≡ Old.paperSUCurvatureConstant
      (+ 2 / 1) Old.configuredInteriorBeta
configuredSU2RateMatchesOld = solve []

configuredSU2RateExact :
  Group.specialUnitaryFourDimensionalRate
    (+ 2 / 1) (+ 1 / 96)
  ≡ + 1 / 2
configuredSU2RateExact = solve []
