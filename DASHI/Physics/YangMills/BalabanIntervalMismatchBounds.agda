module DASHI.Physics.YangMills.BalabanIntervalMismatchBounds where

-- Sufficient shellwise route for bounding a cumulative block correction.
--
-- The canonical theorem permits a direct cumulative estimate and does not
-- require shellwise positivity.  When the source calculation instead supplies
-- pointwise upper/lower bounds on the physical-minus-conditional shell
-- mismatch, this module lifts them by finite ordered summation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _≤ℝ_
  ; +-mono-≤
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )
open import DASHI.Physics.YangMills.BalabanVacuumSubtractedBlockDeterminant using
  ( intervalSumPointwiseSub )

intervalSumMonotone :
  (left right : ℕ → ℝ) →
  (pointwise : ∀ j → left j ≤ℝ right j) →
  ∀ k n →
  intervalSum left k n ≤ℝ intervalSum right k n
intervalSumMonotone left right pointwise k zero = ≤ℝ-refl
  where
    open import DASHI.Foundations.RealAnalysisAxioms using (≤ℝ-refl)
intervalSumMonotone left right pointwise k (suc n) =
  +-mono-≤
    (intervalSumMonotone left right pointwise k n)
    (pointwise (suc (n + k)))

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

intervalMismatchUpperBound :
  (physical conditional upper : ℕ → ℝ) →
  (pointwiseUpper :
    ∀ j →
    physical j -ℝ conditional j ≤ℝ upper j) →
  ∀ k n →
  intervalSum physical k n -ℝ intervalSum conditional k n
    ≤ℝ intervalSum upper k n
intervalMismatchUpperBound
  physical conditional upper pointwiseUpper k n =
  replaceLeft
    (intervalSumPointwiseSub physical conditional k n)
    (intervalSumMonotone
      (λ j → physical j -ℝ conditional j)
      upper
      pointwiseUpper
      k n)

intervalMismatchLowerBound :
  (physical conditional lower : ℕ → ℝ) →
  (pointwiseLower :
    ∀ j →
    lower j ≤ℝ physical j -ℝ conditional j) →
  ∀ k n →
  intervalSum lower k n
    ≤ℝ intervalSum physical k n -ℝ intervalSum conditional k n
intervalMismatchLowerBound
  physical conditional lower pointwiseLower k n =
  replaceRight
    (intervalSumMonotone
      lower
      (λ j → physical j -ℝ conditional j)
      pointwiseLower
      k n)
    (sym (intervalSumPointwiseSub physical conditional k n))
  where
    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y →
      y ≡ x
    sym refl = refl
