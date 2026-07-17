module DASHI.Physics.YangMills.BalabanProjectedBlockToInverseSquare where

-- Direct bilateral coupling consequence of a concrete projected block
-- determinant factorisation.
--
-- The lower and upper correction inputs are stated on the physical-Gaussian
-- versus projected conditional-shell mismatch.  The block determinant theorem
-- is used to identify that mismatch with the cumulative correction before the
-- inverse-square enclosure is formed.  Thus the conditional determinant step,
-- log additivity, and projection linearity are load-bearing rather than unused
-- decoration.

open import Agda.Builtin.Equality using (_≡_; refl)
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
open import DASHI.Physics.YangMills.BalabanProjectedEndpointDifference using
  ( projectedConditionalShell )
open import DASHI.Physics.YangMills.BalabanProjectedBlockCorrection using
  ( projectedEndpointDifference
  ; projectedBlockCorrection
  ; projectedBlockCorrectionGivesCumulativeIdentity
  ; projectedBlockCorrectionEqualsShellMismatch
  )
open import DASHI.Physics.YangMills.BalabanCumulativeDeterminantToInverseSquare using
  ( cumulativeDeterminantBoundsToInverseSquare )

sym :
  ∀ {A : Set} {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

replaceLeft :
  ∀ {a b c : ℝ} →
  a ≡ b →
  b ≤ℝ c →
  a ≤ℝ c
replaceLeft refl b≤c = b≤c

replaceRight :
  ∀ {a b c : ℝ} →
  a ≤ℝ b →
  b ≡ c →
  a ≤ℝ c
replaceRight a≤b refl = a≤b

projectedBlockBoundsToInverseSquareInterval :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (step : BalabanInverseSquareCouplingStep) →
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
  (endpointLower correctionLower interactionLower : ℕ → ℕ → ℝ) →
  (endpointUpper correctionUpper interactionUpper : ℕ → ℕ → ℝ) →
  (endpointLowerBound :
    ∀ k n →
    endpointLower k n
      ≤ℝ projectedEndpointDifference
        determinant logDet projection background vacuum k n) →
  (conditionalMismatchLowerBound :
    ∀ k n →
    correctionLower k n
      ≤ℝ intervalSum gaussian k n
        -ℝ intervalSum
          (projectedConditionalShell
            logDet conditional projection background vacuum)
          k n) →
  (interactionLowerBound :
    ∀ k n →
    interactionLower k n
      ≤ℝ intervalSum interaction k n) →
  (endpointUpperBound :
    ∀ k n →
    projectedEndpointDifference
      determinant logDet projection background vacuum k n
      ≤ℝ endpointUpper k n) →
  (conditionalMismatchUpperBound :
    ∀ k n →
    intervalSum gaussian k n
      -ℝ intervalSum
        (projectedConditionalShell
          logDet conditional projection background vacuum)
        k n
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
  arith step one _*_ assoc rightIdentity
  gaussian interaction totalBeta
  determinant conditional determinantStep
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum
  endpointLower correctionLower interactionLower
  endpointUpper correctionUpper interactionUpper
  endpointLowerBound conditionalMismatchLowerBound interactionLowerBound
  endpointUpperBound conditionalMismatchUpperBound interactionUpperBound
  k n =
  let
    correctionEquality = projectedBlockCorrectionEqualsShellMismatch
      arith one _*_ assoc rightIdentity
      gaussian determinant conditional determinantStep
      logDet logOne logMul
      projection projectionZero projectionAdd
      background vacuum

    correctionLowerBound = λ i length →
      replaceRight
        (conditionalMismatchLowerBound i length)
        (sym (correctionEquality i length))

    correctionUpperBound = λ i length →
      replaceLeft
        (correctionEquality i length)
        (conditionalMismatchUpperBound i length)
  in
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
