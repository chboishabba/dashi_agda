module DASHI.Physics.YangMills.BalabanDeterminantIntervalToPrefix where

-- End-to-end mechanical composition for the finite-cutoff consumer:
--
--   shell identity
--   + endpoint/correction/interaction interval upper bounds
--   + bare inverse-square budget
--   -> BalabanBetaPrefixBound.
--
-- The analytic estimates remain explicit theorem arguments.  No new record or
-- availability surface is introduced.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
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
  ( intervalSum
  ; betaIntervalUpperBound
  )
open import DASHI.Physics.YangMills.BalabanIntervalToPrefixBridge using
  ( intervalUpperBoundToBetaPrefix )

determinantIntervalBoundsToBetaPrefix :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  {γ : ℝ} →
  (threshold : InverseSquareThresholdControlsCoupling K γ step) →
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
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointBound :
    ∀ k n →
    endpoint (n + k) -ℝ endpoint k
      ≤ℝ endpointUpper k n) →
  (correctionBound :
    ∀ k n →
    intervalSum correction k n
      ≤ℝ correctionUpper k n) →
  (interactionBound :
    ∀ k n →
    intervalSum interaction k n
      ≤ℝ interactionUpper k n) →
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
determinantIntervalBoundsToBetaPrefix
  K step threshold
  gaussian correction interaction endpoint
  totalBeta shellDecomposition
  endpointUpper correctionUpper interactionUpper
  endpointBound correctionBound interactionBound
  bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion =
  intervalUpperBoundToBetaPrefix
    K step threshold
    (λ k →
      (endpointUpper zero k +ℝ correctionUpper zero k)
        +ℝ interactionUpper zero k)
    (λ k k≤K →
      betaIntervalUpperBound
        (betaCorrection step)
        gaussian correction interaction endpoint
        totalBeta shellDecomposition
        endpointUpper correctionUpper interactionUpper
        endpointBound correctionBound interactionBound
        zero k)
    bareCouplingBudget
    sourceAuthorityId theoremLocator status noClayPromotion
