module DASHI.Physics.YangMills.BalabanStrongCouplingGroupRicciConstantsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
-- arXiv:2204.12737.
--
-- SOURCE CONSTANTS
--
-- Assumption 1.1 distinguishes the two classical compact matrix groups:
--
--   C_Ric,N(SO(N)) = (N+2)/4 - 1 = (N-2)/4,
--   C_Ric,N(SU(N)) = (N+2)/2 - 1 = N/2.
--
-- In both cases the direct Bakry--Emery Hessian cost is
--
--   8 N |beta| (d-1).
--
-- Thus the SU(N) threshold is |beta| < 1/(16(d-1)), while the
-- SO(N) threshold retains its N dependence.  Corollary 4.8 likewise has
-- distinct susceptibility numerators 8N(d-1) for SO(N) and 16N(d-1)
-- for SU(N).
--
-- DASHI CONTRIBUTION
--
-- Keep the group family in the type of every constant, prove the exact
-- simplifications and configured regressions, and prevent accidental copying
-- of an SO constant into an SU theorem or conversely.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

data ClassicalGaugeFamily : Set where
  orthogonalFamily : ClassicalGaugeFamily
  specialUnitaryFamily : ClassicalGaugeFamily

ricciConstant : ClassicalGaugeFamily → ℚ → ℚ
ricciConstant orthogonalFamily rankN =
  (rankN + (+ 2 / 1)) * (+ 1 / 4) - (+ 1 / 1)
ricciConstant specialUnitaryFamily rankN =
  (rankN + (+ 2 / 1)) * (+ 1 / 2) - (+ 1 / 1)

orthogonalRicciSimplified :
  ∀ rankN →
  ricciConstant orthogonalFamily rankN
  ≡ (rankN - (+ 2 / 1)) * (+ 1 / 4)
orthogonalRicciSimplified rankN = solve (rankN ∷ [])

specialUnitaryRicciSimplified :
  ∀ rankN →
  ricciConstant specialUnitaryFamily rankN
  ≡ rankN * (+ 1 / 2)
specialUnitaryRicciSimplified rankN = solve (rankN ∷ [])

directHessianCost : ℚ → ℚ → ℚ → ℚ
directHessianCost rankN betaMagnitude dMinusOne =
  (+ 8 / 1) * rankN * betaMagnitude * dMinusOne

bakryEmeryRate :
  ClassicalGaugeFamily → ℚ → ℚ → ℚ → ℚ
bakryEmeryRate family rankN betaMagnitude dMinusOne =
  ricciConstant family rankN
    - directHessianCost rankN betaMagnitude dMinusOne

specialUnitaryBakryRateExpanded :
  ∀ rankN betaMagnitude dMinusOne →
  bakryEmeryRate specialUnitaryFamily rankN betaMagnitude dMinusOne
  ≡ rankN
      * ((+ 1 / 2) - (+ 8 / 1) * betaMagnitude * dMinusOne)
specialUnitaryBakryRateExpanded rankN betaMagnitude dMinusOne =
  solve (rankN ∷ betaMagnitude ∷ dMinusOne ∷ [])

orthogonalBakryRateExpanded :
  ∀ rankN betaMagnitude dMinusOne →
  bakryEmeryRate orthogonalFamily rankN betaMagnitude dMinusOne
  ≡ (rankN - (+ 2 / 1)) * (+ 1 / 4)
      - (+ 8 / 1) * rankN * betaMagnitude * dMinusOne
orthogonalBakryRateExpanded rankN betaMagnitude dMinusOne =
  solve (rankN ∷ betaMagnitude ∷ dMinusOne ∷ [])

fourDimensionalDMinusOne : ℚ
fourDimensionalDMinusOne = + 3 / 1

specialUnitaryFourDimensionalRate : ℚ → ℚ → ℚ
specialUnitaryFourDimensionalRate rankN betaMagnitude =
  bakryEmeryRate
    specialUnitaryFamily rankN betaMagnitude fourDimensionalDMinusOne

specialUnitaryFourDimensionalExpanded :
  ∀ rankN betaMagnitude →
  specialUnitaryFourDimensionalRate rankN betaMagnitude
  ≡ rankN * ((+ 1 / 2) - (+ 24 / 1) * betaMagnitude)
specialUnitaryFourDimensionalExpanded rankN betaMagnitude =
  solve (rankN ∷ betaMagnitude ∷ [])

specialUnitaryThreshold : ℚ
specialUnitaryThreshold = + 1 / 48

specialUnitaryThresholdSaturates :
  ∀ rankN →
  specialUnitaryFourDimensionalRate rankN specialUnitaryThreshold
  ≡ + 0 / 1
specialUnitaryThresholdSaturates rankN = solve (rankN ∷ [])

-- A concrete SO(3), d=4 regression.  The exact threshold is
-- (N-2)/(96N), hence 1/288 when N=3.
orthogonalThreeThreshold : ℚ
orthogonalThreeThreshold = + 1 / 288

orthogonalThreeThresholdSaturates :
  bakryEmeryRate
    orthogonalFamily (+ 3 / 1)
    orthogonalThreeThreshold fourDimensionalDMinusOne
  ≡ + 0 / 1
orthogonalThreeThresholdSaturates = solve []

-- Corollary 4.8: the group-specific numerator before multiplication by 1/K_S.
plaquetteSusceptibilityNumerator :
  ClassicalGaugeFamily → ℚ → ℚ → ℚ
plaquetteSusceptibilityNumerator orthogonalFamily rankN dMinusOne =
  (+ 8 / 1) * rankN * dMinusOne
plaquetteSusceptibilityNumerator specialUnitaryFamily rankN dMinusOne =
  (+ 16 / 1) * rankN * dMinusOne

orthogonalFourDimensionalSusceptibilityNumerator :
  ∀ rankN →
  plaquetteSusceptibilityNumerator
    orthogonalFamily rankN fourDimensionalDMinusOne
  ≡ (+ 24 / 1) * rankN
orthogonalFourDimensionalSusceptibilityNumerator rankN =
  solve (rankN ∷ [])

specialUnitaryFourDimensionalSusceptibilityNumerator :
  ∀ rankN →
  plaquetteSusceptibilityNumerator
    specialUnitaryFamily rankN fourDimensionalDMinusOne
  ≡ (+ 48 / 1) * rankN
specialUnitaryFourDimensionalSusceptibilityNumerator rankN =
  solve (rankN ∷ [])

configuredSU2InteriorBeta : ℚ
configuredSU2InteriorBeta = + 1 / 96

configuredSU2BakryRateExact :
  specialUnitaryFourDimensionalRate
    (+ 2 / 1) configuredSU2InteriorBeta
  ≡ + 1 / 2
configuredSU2BakryRateExact = solve []

configuredSU2InverseBakryRate : ℚ
configuredSU2InverseBakryRate = + 2 / 1

configuredSU2SusceptibilityCoefficientExact :
  configuredSU2InverseBakryRate
    * plaquetteSusceptibilityNumerator
        specialUnitaryFamily (+ 2 / 1) fourDimensionalDMinusOne
  ≡ + 192 / 1
configuredSU2SusceptibilityCoefficientExact = solve []
