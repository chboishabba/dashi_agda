module DASHI.Physics.YangMills.BalabanProjectedBlockCorrection where

-- Exact correction between the physical Gaussian beta shells and the
-- simultaneous block determinant endpoint.
--
-- The correction is not assumed shellwise.  On an interval define
--
--   J_{k:n} = sum Gaussian - projectedEndpointDifference.
--
-- The block determinant theorem then identifies J_{k:n} exactly with the
-- difference between the physical Gaussian prefix and the prefix of projected
-- conditional-block log determinants.  Bounding this explicit mismatch is the
-- remaining source-specific penalty calculation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; +-comm
  ; subAddCancelMiddle
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; sub-zero
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra using
  ( vacuumDifference )
open import DASHI.Physics.YangMills.BalabanProjectedEndpointDifference using
  ( projectedConditionalShell
  ; projectedConditionalShellsEqualEndpointDifference
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

restoreDifference :
  (arith : InverseSquareBudgetArithmetic) →
  ∀ total base →
  base +ℝ (total -ℝ base) ≡ total
restoreDifference arith total base =
  let
    p1 = +-comm base (total -ℝ base)
    p2 = cong
      (λ restoredBase → (total -ℝ base) +ℝ restoredBase)
      (sym (sub-zero arith base))
    p3 = subAddCancelMiddle total base 0ℝ
    p4 = sub-zero arith total
  in
    trans p1 (trans p2 (trans p3 p4))

projectedEndpointDifference :
  {Background Scalar : Set} →
  (Background → ℕ → Scalar) →
  (Scalar → ℝ) →
  (ℝ → ℝ) →
  Background → Background →
  ℕ → ℕ → ℝ
projectedEndpointDifference
  determinant logDet projection background vacuum k n =
  projection
    (vacuumDifference
      (λ B → logDet (determinant B (n + k)))
      background vacuum)
  -ℝ projection
    (vacuumDifference
      (λ B → logDet (determinant B k))
      background vacuum)

projectedBlockCorrection :
  {Background Scalar : Set} →
  (ℕ → ℝ) →
  (Background → ℕ → Scalar) →
  (Scalar → ℝ) →
  (ℝ → ℝ) →
  Background → Background →
  ℕ → ℕ → ℝ
projectedBlockCorrection
  gaussian determinant logDet projection background vacuum k n =
  intervalSum gaussian k n
    -ℝ projectedEndpointDifference
      determinant logDet projection background vacuum k n

projectedBlockCorrectionGivesCumulativeIdentity :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (gaussian : ℕ → ℝ) →
  (determinant : Background → ℕ → Scalar) →
  (logDet : Scalar → ℝ) →
  (projection : ℝ → ℝ) →
  (background vacuum : Background) →
  ∀ k n →
  intervalSum gaussian k n
  ≡ projectedEndpointDifference
      determinant logDet projection background vacuum k n
      +ℝ projectedBlockCorrection
        gaussian determinant logDet projection background vacuum k n
projectedBlockCorrectionGivesCumulativeIdentity
  arith gaussian determinant logDet projection background vacuum k n =
  restoreDifference
    arith
    (intervalSum gaussian k n)
    (projectedEndpointDifference
      determinant logDet projection background vacuum k n)

projectedBlockCorrectionEqualsShellMismatch :
  {Background Scalar : Set} →
  (arith : InverseSquareBudgetArithmetic) →
  (one : Scalar) →
  (_*_ : Scalar → Scalar → Scalar) →
  (assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)) →
  (rightIdentity : ∀ a → a * one ≡ a) →
  (gaussian : ℕ → ℝ) →
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
  projectedBlockCorrection
    gaussian determinant logDet projection background vacuum k n
  ≡ intervalSum gaussian k n
      -ℝ intervalSum
        (projectedConditionalShell
          logDet conditional projection background vacuum)
        k n
projectedBlockCorrectionEqualsShellMismatch
  arith one _*_ assoc rightIdentity
  gaussian determinant conditional step
  logDet logOne logMul
  projection projectionZero projectionAdd
  background vacuum k n =
  let
    shellEndpoint = projectedConditionalShellsEqualEndpointDifference
      arith one _*_ assoc rightIdentity
      determinant conditional step
      logDet logOne logMul
      projection projectionZero projectionAdd
      background vacuum k n
  in
    cong
      (λ endpoint → intervalSum gaussian k n -ℝ endpoint)
      (sym shellEndpoint)
