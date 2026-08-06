module DASHI.Physics.YangMills.BalabanP33StrictDiscountedMarginFactorizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban III. Convergence".
-- DOI: 10.1007/s00023-013-0303-3.
--
-- DASHI CONTRIBUTION
--
-- Close the division-free algebra behind the strict infinite discounted-loss
-- margin.  Write D = 2-theta and supply invD*D=1.  Then
--
--   m_* = 1/32 - invD E
--
-- satisfies the exact identity
--
--   D m_* = D/32 - E.
--
-- Thus the physically meaningful strict budget is the cross-multiplied
-- inequality E < D/32, not the bare assertion theta<2 by itself.  Positivity of
-- D and the physical geometric loss estimate remain separate analytic inputs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

terminalGap : ℚ
terminalGap = + 1 / 32

discountDenominator : ℚ → ℚ
discountDenominator theta = (+ 2 / 1) - theta

survivingMargin : ℚ → ℚ → ℚ → ℚ
survivingMargin theta inverseDenominator errorAmplitude =
  terminalGap - inverseDenominator * errorAmplitude

crossMultipliedBudgetGap : ℚ → ℚ → ℚ
crossMultipliedBudgetGap theta errorAmplitude =
  discountDenominator theta * terminalGap - errorAmplitude

strictMarginFactorization :
  ∀ theta inverseDenominator errorAmplitude →
  inverseDenominator * discountDenominator theta ≡ 1ℚ →
  discountDenominator theta
    * survivingMargin theta inverseDenominator errorAmplitude
  ≡ crossMultipliedBudgetGap theta errorAmplitude
strictMarginFactorization theta inverseDenominator errorAmplitude inverseLaw
  rewrite inverseLaw =
  solve (theta ∷ inverseDenominator ∷ errorAmplitude ∷ [])

configuredBudgetGapExpanded :
  ∀ theta errorAmplitude →
  crossMultipliedBudgetGap theta errorAmplitude
  ≡ ((+ 2 / 1) - theta) * (+ 1 / 32) - errorAmplitude
configuredBudgetGapExpanded theta errorAmplitude =
  solve (theta ∷ errorAmplitude ∷ [])

thirtyTwoScaledBudgetGap :
  ∀ theta errorAmplitude →
  (+ 32 / 1) * crossMultipliedBudgetGap theta errorAmplitude
  ≡ ((+ 2 / 1) - theta) - (+ 32 / 1) * errorAmplitude
thirtyTwoScaledBudgetGap theta errorAmplitude =
  solve (theta ∷ errorAmplitude ∷ [])

record StrictPhysicalDiscountedLossTarget : Set where
  constructor strictPhysicalDiscountedLossTarget
  field
    theta errorAmplitude inverseDenominator : ℚ
    inverseDenominatorLaw :
      inverseDenominator * discountDenominator theta ≡ 1ℚ
    denominatorPositive : Set
    physicalLossRate : Set
    crossMultipliedGapPositive : Set

-- The exact algebraic identity is proved above.  The target does not replace
-- the physical estimates epsilon_B,j + epsilon_R,j <= E theta^j, theta<2, or
-- the strict numerical inequality 32E < 2-theta.
