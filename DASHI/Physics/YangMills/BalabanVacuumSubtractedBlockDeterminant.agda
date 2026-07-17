module DASHI.Physics.YangMills.BalabanVacuumSubtractedBlockDeterminant where

-- Vacuum-subtracted form of the finite block-Cholesky log identity.
--
-- Pointwise block determinant factorisation at a background and at the vacuum
-- implies that the vacuum-subtracted endpoint log determinant evolves by the
-- sum of vacuum-subtracted conditional shell logs.  Background-independent
-- determinant factors therefore disappear before the beta projection.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; subSelf
  ; subAddDistributes
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanBlockDeterminantLogAdditivity using
  ( conditionalLogShell
  ; blockDeterminantLogIntervalFromStep
  )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra using
  ( vacuumDifference )

intervalSumPointwiseSub :
  (left right : ℕ → ℝ) →
  ∀ k n →
  intervalSum left k n -ℝ intervalSum right k n
    ≡ intervalSum (λ j → left j -ℝ right j) k n
intervalSumPointwiseSub left right k zero = subSelf 0ℝ
intervalSumPointwiseSub left right k (suc n) =
  let
    index = suc (n + k)
    p1 = subAddDistributes
      (intervalSum left k n)
      (left index)
      (intervalSum right k n)
      (right index)
    p2 = cong
      (λ prefixDifference →
        prefixDifference +ℝ (left index -ℝ right index))
      (intervalSumPointwiseSub left right k n)
  in
    trans p1 p2

vacuumSubtractedBlockDeterminantInterval :
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
  (background vacuum : Background) →
  ∀ k n →
  vacuumDifference
    (λ B → logDet (determinant B (n + k)))
    background vacuum
  ≡ vacuumDifference
      (λ B → logDet (determinant B k))
      background vacuum
      +ℝ intervalSum
        (λ shell →
          conditionalLogShell logDet (conditional background) shell
            -ℝ conditionalLogShell logDet (conditional vacuum) shell)
        k n
vacuumSubtractedBlockDeterminantInterval
  one _*_ assoc rightIdentity
  determinant conditional step
  logDet logOne logMul
  background vacuum k n =
  let
    endBackground = blockDeterminantLogIntervalFromStep
      one _*_ assoc rightIdentity
      (determinant background)
      (conditional background)
      (step background)
      logDet logOne logMul k n
    endVacuum = blockDeterminantLogIntervalFromStep
      one _*_ assoc rightIdentity
      (determinant vacuum)
      (conditional vacuum)
      (step vacuum)
      logDet logOne logMul k n

    backgroundShell =
      conditionalLogShell logDet (conditional background)
    vacuumShell =
      conditionalLogShell logDet (conditional vacuum)

    p1 = cong
      (λ endValue →
        endValue -ℝ logDet (determinant vacuum (n + k)))
      endBackground
    p2 = cong
      (λ vacuumEnd →
        (logDet (determinant background k)
          +ℝ intervalSum backgroundShell k n)
          -ℝ vacuumEnd)
      endVacuum
    p3 = subAddDistributes
      (logDet (determinant background k))
      (intervalSum backgroundShell k n)
      (logDet (determinant vacuum k))
      (intervalSum vacuumShell k n)
    p4 = cong
      (λ shellDifference →
        vacuumDifference
          (λ B → logDet (determinant B k))
          background vacuum
          +ℝ shellDifference)
      (intervalSumPointwiseSub backgroundShell vacuumShell k n)
  in
    trans p1 (trans p2 (trans p3 p4))
