module DASHI.Physics.YangMills.BalabanProjectionIntervalLinearity where

-- Finite linearity required to apply CMP 109's beta/polarisation projection to
-- a cumulative vacuum-subtracted determinant identity.
--
-- An additive projection commutes with every finite interval sum.  Applying it
-- to the block-Cholesky identity therefore yields an endpoint projected
-- determinant difference plus the sum of projected conditional-shell terms.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanBlockDeterminantLogAdditivity using
  ( conditionalLogShell )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra using
  ( vacuumDifference )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractedBlockDeterminant using
  ( vacuumSubtractedBlockDeterminantInterval )

projectionIntervalSum :
  (projection : ℝ → ℝ) →
  projection 0ℝ ≡ 0ℝ →
  (∀ a b → projection (a +ℝ b) ≡ projection a +ℝ projection b) →
  (shell : ℕ → ℝ) →
  ∀ k n →
  projection (intervalSum shell k n)
    ≡ intervalSum (λ j → projection (shell j)) k n
projectionIntervalSum projection projectionZero projectionAdd shell k zero =
  projectionZero
projectionIntervalSum projection projectionZero projectionAdd shell k (suc n) =
  let
    index = suc (n + k)
    p1 = projectionAdd
      (intervalSum shell k n)
      (shell index)
    p2 = cong
      (λ prefix → prefix +ℝ projection (shell index))
      (projectionIntervalSum
        projection projectionZero projectionAdd shell k n)
  in
    trans p1 p2

projectedVacuumSubtractedBlockDeterminantInterval :
  {Background Scalar : Set} →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
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
  projection
    (vacuumDifference
      (λ B → logDet (determinant B (n + k)))
      background vacuum)
  ≡ projection
      (vacuumDifference
        (λ B → logDet (determinant B k))
        background vacuum)
      +ℝ intervalSum
        (λ shell →
          projection
            (conditionalLogShell logDet (conditional background) shell
              -ℝ conditionalLogShell logDet (conditional vacuum) shell))
        k n
projectedVacuumSubtractedBlockDeterminantInterval
  one _*_ assoc rightIdentity
  determinant conditional step
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum k n =
  let
    shellDifference = λ shell →
      conditionalLogShell logDet (conditional background) shell
        -ℝ conditionalLogShell logDet (conditional vacuum) shell

    blockIdentity = vacuumSubtractedBlockDeterminantInterval
      one _*_ assoc rightIdentity
      determinant conditional step
      logDet logOne logMul
      background vacuum k n

    p1 = cong projection blockIdentity
    p2 = projectionAdd
      (vacuumDifference
        (λ B → logDet (determinant B k))
        background vacuum)
      (intervalSum shellDifference k n)
    p3 = cong
      (λ projectedShells →
        projection
          (vacuumDifference
            (λ B → logDet (determinant B k))
            background vacuum)
          +ℝ projectedShells)
      (projectionIntervalSum
        projection projectionZero projectionAdd
        shellDifference k n)
  in
    trans p1 (trans p2 p3)
