module DASHI.Physics.YangMills.BalabanLinearInverseSquareEnclosure where

-- Linear bilateral coupling consequence of the cumulative determinant route.
--
-- The result has the exact discrete form of Bałaban's bilateral logarithmic
-- estimate in the inverse-square coordinate:
--
--   u_k - betaUpper * n <= u_{k+n}
--   u_{k+n} <= u_k - betaLower * n.
--
-- The six analytic component estimates remain theorem arguments.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
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
open import DASHI.Physics.YangMills.BalabanLinearIntervalEnclosure using
  ( fromNatℝ
  ; betaLinearIntervalBilateralBound
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareIntervalIdentity using
  ( inverseSquareIntervalEnclosure )

linearDeterminantBoundsToInverseSquareEnclosure :
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
  (endpointLowerSlope correctionLowerSlope interactionLowerSlope : ℝ) →
  (endpointUpperSlope correctionUpperSlope interactionUpperSlope : ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLowerSlope *ℝ fromNatℝ n
      ≤ℝ endpoint (n + k) -ℝ endpoint k) →
  (correctionLowerBound :
    ∀ k n →
    correctionLowerSlope *ℝ fromNatℝ n
      ≤ℝ intervalSum correction k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLowerSlope *ℝ fromNatℝ n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpperSlope *ℝ fromNatℝ n) →
  (correctionUpperBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpperSlope *ℝ fromNatℝ n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpperSlope *ℝ fromNatℝ n) →
  ∀ k n →
  (inverseSquaredCoupling step k
      -ℝ (((endpointUpperSlope +ℝ correctionUpperSlope)
            +ℝ interactionUpperSlope) *ℝ fromNatℝ n)
      ≤ℝ inverseSquaredCoupling step (n + k))
  ×
  (inverseSquaredCoupling step (n + k)
      ≤ℝ inverseSquaredCoupling step k
          -ℝ (((endpointLowerSlope +ℝ correctionLowerSlope)
                +ℝ interactionLowerSlope) *ℝ fromNatℝ n))
linearDeterminantBoundsToInverseSquareEnclosure
  arith step gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointLowerSlope correctionLowerSlope interactionLowerSlope
  endpointUpperSlope correctionUpperSlope interactionUpperSlope
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  let
    betaBounds = betaLinearIntervalBilateralBound
      (betaCorrection step)
      gaussian correction interaction endpoint
      totalBeta shellDecomposition
      endpointLowerSlope correctionLowerSlope interactionLowerSlope
      endpointUpperSlope correctionUpperSlope interactionUpperSlope
      endpointLowerBound correctionLowerBound interactionLowerBound
      endpointUpperBound correctionUpperBound interactionUpperBound
  in
    inverseSquareIntervalEnclosure
      arith step
      (λ i length →
        ((endpointLowerSlope +ℝ correctionLowerSlope)
          +ℝ interactionLowerSlope) *ℝ fromNatℝ length)
      (λ i length →
        ((endpointUpperSlope +ℝ correctionUpperSlope)
          +ℝ interactionUpperSlope) *ℝ fromNatℝ length)
      (λ i length → proj₁ (betaBounds i length))
      (λ i length → proj₂ (betaBounds i length))
      k n
