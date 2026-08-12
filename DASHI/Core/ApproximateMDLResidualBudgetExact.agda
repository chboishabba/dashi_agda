module DASHI.Core.ApproximateMDLResidualBudgetExact where

------------------------------------------------------------------------
-- APPROXIMATE MDL / RESIDUAL-BUDGET BRIDGE
--
-- Reference / motivation:
--
-- Qian Li, Xinyu Mao, Shang-Hua Teng, Guangxu Yang,
-- "Prediction Under Imperfect Compression: A Theory of Approximate MDL",
-- arXiv:2606.04834v1 (2026).
-- No DOI is asserted for the arXiv preprint.
--
-- Their theorem distinguishes fixed additive approximation from
-- multiplicative approximation in sequential MDL prediction.  The finite
-- arithmetic below is only the DASHI residual-budget analogue: fixed additive
-- slack does not grow with carrier complexity, while scale-relative slack can.
-- It does NOT import the paper's statistical theorem as an Agda proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_)

data ResidualBudgetMode : Set where
  fixedAdditive : ResidualBudgetMode
  scaleRelative : ResidualBudgetMode

allowedSlack :
  ResidualBudgetMode → Nat → Nat → Nat
allowedSlack fixedAdditive parameter complexity = parameter
allowedSlack scaleRelative parameter complexity = parameter * complexity

fixedSlackIgnoresComplexity :
  (C n : Nat) →
  allowedSlack fixedAdditive C n ≡ C
fixedSlackIgnoresComplexity C n = refl

unitScaleSlackAtThree :
  allowedSlack scaleRelative 1 3 ≡ 3
unitScaleSlackAtThree = refl

unitFixedSlackAtThree :
  allowedSlack fixedAdditive 1 3 ≡ 1
unitFixedSlackAtThree = refl

record WithinResidualBudget
    (cost allowance : Nat) : Set where
  constructor withinResidualBudget
  field
    slack : Nat
    budgetExact : cost + slack ≡ allowance

open WithinResidualBudget public

costTwoFitsUnitScaleAtThree :
  WithinResidualBudget 2 (allowedSlack scaleRelative 1 3)
costTwoFitsUnitScaleAtThree =
  withinResidualBudget 1 refl

costTwoDoesNotFitFixedUnit :
  WithinResidualBudget 2 (allowedSlack fixedAdditive 1 3) → ⊥
costTwoDoesNotFitFixedUnit (withinResidualBudget zero ())
costTwoDoesNotFitFixedUnit (withinResidualBudget (suc slack) ())

record ApproximateMDLResidualBoundary : Set where
  constructor approximateMDLResidualBoundary
  field
    fixedAdditiveSlackIsComplexityIndependent : Bool
    fixedAdditiveSlackIsComplexityIndependentIsTrue :
      fixedAdditiveSlackIsComplexityIndependent ≡ true
    scaleRelativeSlackCanGrowWithComplexity : Bool
    scaleRelativeSlackCanGrowWithComplexityIsTrue :
      scaleRelativeSlackCanGrowWithComplexity ≡ true
    paperStatisticalGuaranteeProvedHere : Bool
    paperStatisticalGuaranteeProvedHereIsFalse :
      paperStatisticalGuaranteeProvedHere ≡ false

canonicalApproximateMDLResidualBoundary :
  ApproximateMDLResidualBoundary
canonicalApproximateMDLResidualBoundary =
  approximateMDLResidualBoundary
    true refl
    true refl
    false refl
