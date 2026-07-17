module DASHI.Physics.YangMills.BalabanProjectedBlockBetaIdentity where

-- Canonical exact identity produced by the simultaneous block route.
--
-- The theorem returns both:
--
--   sum beta = projectedEndpointDifference + J_{k:n} + sum interaction,
--
-- and the non-tautological identification
--
--   J_{k:n} = sum Gaussian - sum projectedConditionalShell.
--
-- Thus the remaining analytic theorem is precisely a bound on the mismatch
-- between the physical Gaussian shells and the block-Cholesky conditional
-- factors.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_×_; _,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanProjectedEndpointDifference using
  ( projectedConditionalShell )
open import DASHI.Physics.YangMills.BalabanProjectedBlockCorrection using
  ( projectedEndpointDifference
  ; projectedBlockCorrection
  ; projectedBlockCorrectionGivesCumulativeIdentity
  ; projectedBlockCorrectionEqualsShellMismatch
  )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantInterval using
  ( cumulativeDeterminantBetaEquality )

projectedBlockBetaIdentityAndCorrection :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (beta gaussian interaction : ℕ → ℝ) →
  (totalBeta :
    ∀ j →
    beta (suc j)
      ≡ gaussian (suc j) +ℝ interaction (suc j)) →
  (determinant conditional : Background → ℕ → Scalar) →
  (step :
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
  ∀ k n →
  (intervalSum beta k n
    ≡ (projectedEndpointDifference
          determinant logDet projection background vacuum k n
        +ℝ projectedBlockCorrection
          gaussian determinant logDet projection background vacuum k n)
        +ℝ intervalSum interaction k n)
  ×
  (projectedBlockCorrection
      gaussian determinant logDet projection background vacuum k n
    ≡ intervalSum gaussian k n
        -ℝ intervalSum
          (projectedConditionalShell
            logDet conditional projection background vacuum)
          k n)
projectedBlockBetaIdentityAndCorrection
  arith one _*_ assoc rightIdentity
  beta gaussian interaction totalBeta
  determinant conditional step
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum k n =
  cumulativeDeterminantBetaEquality
    beta gaussian interaction
    (projectedEndpointDifference
      determinant logDet projection background vacuum)
    (projectedBlockCorrection
      gaussian determinant logDet projection background vacuum)
    totalBeta
    (projectedBlockCorrectionGivesCumulativeIdentity
      arith gaussian determinant logDet projection background vacuum)
    k n
  ,
  projectedBlockCorrectionEqualsShellMismatch
    arith one _*_ assoc rightIdentity
    gaussian determinant conditional step
    logDet logOne logMul
    projection projectionZero projectionAdd
    background vacuum k n
