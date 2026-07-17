module DASHI.Physics.YangMills.BalabanProjectedBlockToInverseSquare where

-- Direct bilateral coupling consequence of a concrete projected block
-- determinant factorisation.
--
-- This is the Theorem-2-facing counterpart of the CMP 122 upper-budget route:
-- endpoint, exact block-correction, and interaction lower/upper bounds produce
-- bilateral inverse-square control on every interval.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
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
open import DASHI.Physics.YangMills.BalabanProjectedBlockCorrection using
  ( projectedEndpointDifference
  ; projectedBlockCorrection
  ; projectedBlockCorrectionGivesCumulativeIdentity
  )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantToInverseSquare using
  ( cumulativeDeterminantBoundsToInverseSquare )

projectedBlockBoundsToInverseSquareInterval :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
  (gaussian interaction : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (determinant : Background → ℕ → Scalar) →
  (logDet : Scalar → ℝ) →
  (projection : ℝ → ℝ) →
  (background vacuum : Background) →
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n
      ≤ℝ projectedEndpointDifference
        determinant logDet projection background vacuum k n) →
  (correctionLowerBound :
    ∀ k n →
    correctionLower k n
      ≤ℝ projectedBlockCorrection
        gaussian determinant logDet projection background vacuum k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    projectedEndpointDifference
      determinant logDet projection background vacuum k n
      ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    projectedBlockCorrection
      gaussian determinant logDet projection background vacuum k n
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
projectedBlockBoundsToInverseSquareInterval
  arith step gaussian interaction totalBeta
  determinant logDet projection background vacuum
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound correctionLowerBound interactionLowerBound
  endpointUpperBound correctionUpperBound interactionUpperBound
  k n =
  cumulativeDeterminantBoundsToInverseSquare
    arith step gaussian interaction
    (projectedEndpointDifference
      determinant logDet projection background vacuum)
    (projectedBlockCorrection
      gaussian determinant logDet projection background vacuum)
    totalBeta
    (projectedBlockCorrectionGivesCumulativeIdentity
      arith gaussian determinant logDet projection background vacuum)
    endpointLower correctionLower interactionLower
    endpointUpper correctionUpper interactionUpper
    endpointLowerBound correctionLowerBound interactionLowerBound
    endpointUpperBound correctionUpperBound interactionUpperBound
    k n
