module DASHI.Physics.YangMills.BalabanCumulativeDeterminantToInverseSquare where

-- Canonical cumulative determinant-to-coupling composition.  Unlike the
-- stronger shell-resolved specialisation, this theorem requires only the
-- block-level identity
--
--   sum Gaussian = endpointDifference + J_{k:n}.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_×_; proj₁; proj₂)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _≤ℝ_
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantInterval using
  ( cumulativeDeterminantBetaBilateralBound )
open import DASHI.Physics.YangMills.BalabanInverseSquareIntervalIdentity using
  ( inverseSquareIntervalEnclosure )

cumulativeDeterminantBoundsToInverseSquare :
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  (gaussian interaction : ℕ → ℝ) →
  (endpointDifference cumulativeCorrection : ℕ → ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (cumulativeGaussianIdentity :
    ∀ k n →
    intervalSum gaussian k n
      ≡ endpointDifference k n +ℝ cumulativeCorrection k n) →
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n ≤ℝ endpointDifference k n) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n ≤ℝ cumulativeCorrection k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpointDifference k n ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    cumulativeCorrection k n ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n ≤ℝ interactionUpper k n) →
  ∀ k n →
  (inverseSquaredCoupling step k
      -ℝ ((endpointUpper k n +ℝ correctionUpper k n)
          +ℝ interactionUpper k n)
      ≤ℝ inverseSquaredCoupling step (n + k))
  ×
  (inverseSquaredCoupling step (n + k)
      ≤ℝ inverseSquaredCoupling step k
          -ℝ ((endpointLower k n +ℝ correctionLower k n)
              +ℝ interactionLower k n))
cumulativeDeterminantBoundsToInverseSquare
  arith step gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  let
    betaBounds = cumulativeDeterminantBetaBilateralBound
      (betaCorrection step)
      gaussian interaction
      endpointDifference cumulativeCorrection
      totalBeta cumulativeGaussianIdentity
      endpointLower correctionLower interactionLower
      endpointUpper correctionUpper interactionUpper
      endpointLowerBound correctionLowerBound interactionLowerBound
      endpointUpperBound correctionUpperBound interactionUpperBound
  in
    inverseSquareIntervalEnclosure
      arith step
      (λ i length →
        (endpointLower i length +ℝ correctionLower i length)
          +ℝ interactionLower i length)
      (λ i length →
        (endpointUpper i length +ℝ correctionUpper i length)
          +ℝ interactionUpper i length)
      (λ i length → proj₁ (betaBounds i length))
      (λ i length → proj₂ (betaBounds i length))
      k n
