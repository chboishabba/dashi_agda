module DASHI.Physics.YangMills.BalabanCumulativeDeterminantToPrefix where

-- Canonical block-level route into the existing beta-prefix consumer.  This
-- theorem does not require or manufacture a shellwise endpoint telescope.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _≤ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using
  ( clayYangMillsPromoted )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareThresholdControlsCoupling
  ; gammaInverseSquare
  ; BalabanBetaPrefixBound
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantInterval using
  ( cumulativeDeterminantBetaUpperBound )
open import DASHI.Physics.YangMills.BalabanIntervalToPrefixBridge using
  ( intervalUpperBoundToBetaPrefix )

cumulativeDeterminantBoundsToBetaPrefix :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  {γ : ℝ} →
  (threshold : InverseSquareThresholdControlsCoupling K γ step) →
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
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointUpperBound :
    ∀ k n →
    endpointDifference k n ≤ℝ endpointUpper k n) →
  (correctionUpperBound :
    ∀ k n →
    cumulativeCorrection k n ≤ℝ correctionUpper k n) →
  (interactionUpperBound :
    ∀ k n →
    intervalSum interaction k n ≤ℝ interactionUpper k n) →
  (bareCouplingBudget :
    ∀ k → k ≤ K →
    gammaInverseSquare threshold
      +ℝ ((endpointUpper zero k +ℝ correctionUpper zero k)
          +ℝ interactionUpper zero k)
      ≤ℝ inverseSquaredCoupling step zero) →
  (sourceAuthorityId : SourceAuthorityId) →
  (theoremLocator : String) →
  (status : VerificationStatus) →
  (noClayPromotion : clayYangMillsPromoted ≡ false) →
  BalabanBetaPrefixBound K step threshold
cumulativeDeterminantBoundsToBetaPrefix
  K step threshold
  gaussian interaction
  endpointDifference cumulativeCorrection
  totalBeta cumulativeGaussianIdentity
  endpointUpper correctionUpper interactionUpper
  endpointUpperBound correctionUpperBound interactionUpperBound
  bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion =
  intervalUpperBoundToBetaPrefix
    K step threshold
    (λ k →
      (endpointUpper zero k +ℝ correctionUpper zero k)
        +ℝ interactionUpper zero k)
    (λ k k≤K →
      cumulativeDeterminantBetaUpperBound
        (betaCorrection step)
        gaussian interaction
        endpointDifference cumulativeCorrection
        totalBeta cumulativeGaussianIdentity
        endpointUpper correctionUpper interactionUpper
        endpointUpperBound correctionUpperBound interactionUpperBound
        zero k)
    bareCouplingBudget
    sourceAuthorityId theoremLocator status noClayPromotion
