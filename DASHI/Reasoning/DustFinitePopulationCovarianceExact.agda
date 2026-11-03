module DASHI.Reasoning.DustFinitePopulationCovarianceExact where

-- DUST original method: Dahal, Mandal, Gülbahar, Vegesna.
-- DASHI contribution: finite rational affine-estimator audit.
-- Source-written theorem candidates; no kernel receipt or CI.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _/_; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Reasoning.DustTwoProbeCenteringExact as Two

half : ℚ
half = + 1 / 2

affineLoss : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
affineLoss g h sigma offset draw =
  g * (h + sigma * draw) + offset

meanLoss : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
meanLoss g h sigma offset a b =
  half * (affineLoss g h sigma offset a +
          affineLoss g h sigma offset b)

-- Population mean, NOT clean baseline. Original Dust uses negative
-- reward-weighted perturbation with loss reduction convention.
dustAffineTwo : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
dustAffineTwo g h sigmaInv sigma offset a b =
  - (half * sigmaInv *
    (((meanLoss g h sigma offset a b +
        - affineLoss g h sigma offset a) * a) +
     ((meanLoss g h sigma offset a b +
        - affineLoss g h sigma offset b) * b)))

-- No inversion assumption for the following pure polynomial identity:
dustAffineTwoCovarianceFactor :
  (g h sigmaInv sigma offset a b : ℚ) →
  dustAffineTwo g h sigmaInv sigma offset a b
    ≡ (sigmaInv * sigma) * (g * Two.centeredTwoCredit a b)
dustAffineTwoCovarianceFactor g h sigmaInv sigma offset a b =
  Ring.solve-∀ g h sigmaInv sigma offset a b

-- Explicit inverse-amplitude condition, rather than dividing by zero.
dustAffineTwoIsSampleCovariance :
  (g h sigmaInv sigma offset a b : ℚ) →
  sigmaInv * sigma ≡ 1ℚ →
  dustAffineTwo g h sigmaInv sigma offset a b
    ≡ g * Two.centeredTwoCredit a b
dustAffineTwoIsSampleCovariance g h sigmaInv sigma offset a b inv =
  trans (dustAffineTwoCovarianceFactor g h sigmaInv sigma offset a b)
    (trans (cong (λ s → s * (g * Two.centeredTwoCredit a b)) inv)
      (Ring.solve-∀ g a b))

-- Exact two-probe result: gradient times finite sample covariance.
dustAffineTwoDifferenceSquare :
  (g h sigmaInv sigma offset a b : ℚ) →
  sigmaInv * sigma ≡ 1ℚ →
  dustAffineTwo g h sigmaInv sigma offset a b
    ≡ g * (Two.quarter * ((a + - b) * (a + - b)))
dustAffineTwoDifferenceSquare g h sigmaInv sigma offset a b inv =
  trans (dustAffineTwoIsSampleCovariance g h sigmaInv sigma offset a b inv)
    (cong (λ v → g * v) (Two.twoProbeCenteredSquare a b))
