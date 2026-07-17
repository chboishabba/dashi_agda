module DASHI.Physics.YangMills.BalabanDeterminantToInverseSquareInterval where

-- Direct composition from the cumulative determinant decomposition to the
-- inverse-square coupling enclosure.
--
-- This theorem packages no analytic premise into a record.  It takes the
-- literal shell equalities and componentwise interval estimates as arguments,
-- proves the bilateral beta bound, and feeds it into the exact recurrence
-- telescope.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc; _+_)
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
open import DASHI.Physics.YangMills.BalabanBilateralIntervalBounds using
  ( betaIntervalBilateralBound )
open import DASHI.Physics.YangMills.BalabanInverseSquareIntervalIdentity using
  ( inverseSquareIntervalEnclosure )

-- The endpoint, correction, and interaction bounds are kept separately in the
-- statement so the source calculation cannot hide the penalty contribution.
determinantBoundsToInverseSquareInterval :
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  (gaussian correction interaction endpoint : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (shellDecomposition :
    ∀ j →
    gaussian (suc j)
      ≡ (endpoint (suc j) -ℝ endpoint j)
          +ℝ correction (suc j)) →
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n
      ≤ℝ endpoint (n + k) -ℝ endpoint k) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n
      ≤ℝ intervalSum correction k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpper k n) →
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
determinantBoundsToInverseSquareInterval
  arith step gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  inverseSquareIntervalEnclosure
    arith
    step
    (λ i length →
      (endpointLower i length +ℝ correctionLower i length)
        +ℝ interactionLower i length)
    (λ i length →
      (endpointUpper i length +ℝ correctionUpper i length)
        +ℝ interactionUpper i length)
    (λ i length →
      proj₁
        (betaIntervalBilateralBound
          (betaCorrection step)
          gaussian correction interaction endpoint
          totalBeta shellDecomposition
          endpointLower correctionLower interactionLower
          endpointUpper correctionUpper interactionUpper
          endpointLowerBound correctionLowerBound interactionLowerBound
          endpointUpperBound correctionUpperBound interactionUpperBound
          i length))
    (λ i length →
      proj₂
        (betaIntervalBilateralBound
          (betaCorrection step)
          gaussian correction interaction endpoint
          totalBeta shellDecomposition
          endpointLower correctionLower interactionLower
          endpointUpper correctionUpper interactionUpper
          endpointLowerBound correctionLowerBound interactionLowerBound
          endpointUpperBound correctionUpperBound interactionUpperBound
          i length))
    k n
