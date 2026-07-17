module DASHI.Physics.YangMills.BalabanProjectedBlockToCMP122 where

-- Direct end-to-end composition from a concrete simultaneous block determinant
-- factorisation to the existing CMP 122 closure.
--
-- The source-facing inputs remain explicit:
--
--   * the physical beta = Gaussian + interaction shell identity;
--   * the one-step conditional block determinant factorisation;
--   * log-determinant additivity and projection linearity;
--   * upper bounds for the projected endpoint difference, the exact projected
--     block correction, and the interaction prefix;
--   * the bare inverse-square budget.
--
-- No adjacent determinant telescope and no analytic availability record is
-- introduced.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _≤ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using
  ( clayYangMillsPromoted )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  )
open import DASHI.Physics.YangMills.BalabanSection2InductivePackage using
  ( UniformBalabanRGClosure
  ; BalabanSection2InductivePackage
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; InverseSquareBudgetOrderBridge
  ; InverseSquareThresholdControlsCoupling
  ; gammaInverseSquare
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanProjectedBlockCorrection using
  ( projectedEndpointDifference
  ; projectedBlockCorrection
  ; projectedBlockCorrectionGivesCumulativeIdentity
  )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantToCMP122 using
  ( cumulativeDeterminantBoundsToFiniteCutoffRG )
open import DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure using
  ( BalabanCMP122ConditionalTheorem
  ; γ
  ; section2Package
  )

projectedBlockBoundsToFiniteCutoffRG :
  {Background Scalar : Set} →
  (theorem : BalabanCMP122ConditionalTheorem) →
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (threshold :
    InverseSquareThresholdControlsCoupling K (γ theorem) step) →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (gaussian interaction : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    betaCorrection step (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (determinant conditional : Background → ℕ → Scalar) →
  (determinantStep :
    ∀ B j →
    determinant B (suc j)
      ≡ determinant B j * conditional B j) →
  (logDet : Scalar → ℝ) →
  logDet one ≡ 0ℝ →
  (logMul : ∀ a b → logDet (a * b) ≡ logDet a +ℝ logDet b) →
  (projection : ℝ → ℝ) →
  projection 0ℝ ≡ 0ℝ →
  (projectionAdd :
    ∀ a b →
    projection (a +ℝ b)
      ≡ projection a +ℝ projection b) →
  (background vacuum : Background) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
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
  BalabanSection2InductivePackage.terminalScale (section2Package theorem)
    ≤ K →
  UniformBalabanRGClosure
projectedBlockBoundsToFiniteCutoffRG
  theorem arith order K step threshold
  one _*_ assoc rightIdentity
  gaussian interaction totalBeta
  determinant conditional determinantStep
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum
  endpointUpper correctionUpper interactionUpper
  endpointUpperBound correctionUpperBound interactionUpperBound
  bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion
  sourceTerminal≤K =
  cumulativeDeterminantBoundsToFiniteCutoffRG
    theorem arith order K step threshold
    gaussian interaction
    (projectedEndpointDifference
      determinant logDet projection background vacuum)
    (projectedBlockCorrection
      gaussian determinant logDet projection background vacuum)
    totalBeta
    (projectedBlockCorrectionGivesCumulativeIdentity
      arith gaussian determinant logDet projection background vacuum)
    endpointUpper correctionUpper interactionUpper
    endpointUpperBound correctionUpperBound interactionUpperBound
    bareCouplingBudget
    sourceAuthorityId theoremLocator status noClayPromotion
    sourceTerminal≤K
