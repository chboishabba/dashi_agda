module DASHI.Physics.YangMills.BalabanVacuumSubtractionAlgebra where

-- Algebra of Bałaban's background-minus-vacuum subtraction.
--
-- In particular, a background-independent basis, coordinate, or determinant
-- normalisation contributes the same additive constant at B and at the vacuum,
-- and therefore cancels exactly.  The result is proved rather than hidden in a
-- comment or status flag.

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; +-identityʳ
  ; subSelf
  ; subAddDistributes
  ; cong
  ; trans
  )

vacuumDifference :
  {Background : Set} →
  (Background → ℝ) →
  Background → Background →
  ℝ
vacuumDifference observable background vacuum =
  observable background -ℝ observable vacuum

vacuumDifferenceAdditive :
  {Background : Set} →
  (left right : Background → ℝ) →
  (background vacuum : Background) →
  vacuumDifference (λ B → left B +ℝ right B) background vacuum
    ≡ vacuumDifference left background vacuum
        +ℝ vacuumDifference right background vacuum
vacuumDifferenceAdditive left right background vacuum =
  subAddDistributes
    (left background)
    (right background)
    (left vacuum)
    (right vacuum)

backgroundIndependentTermCancels :
  {Background : Set} →
  (observable variablePart : Background → ℝ) →
  (constant : ℝ) →
  (decomposition :
    ∀ B →
    observable B ≡ variablePart B +ℝ constant) →
  (background vacuum : Background) →
  vacuumDifference observable background vacuum
    ≡ vacuumDifference variablePart background vacuum
backgroundIndependentTermCancels
  observable variablePart constant decomposition background vacuum =
  let
    p1 = cong
      (λ value → value -ℝ observable vacuum)
      (decomposition background)
    p2 = cong
      (λ value →
        (variablePart background +ℝ constant) -ℝ value)
      (decomposition vacuum)
    p3 = subAddDistributes
      (variablePart background)
      constant
      (variablePart vacuum)
      constant
    p4 = cong
      (λ cancelled →
        vacuumDifference variablePart background vacuum +ℝ cancelled)
      (subSelf constant)
    p5 = +-identityʳ
      (vacuumDifference variablePart background vacuum)
  in
    trans p1 (trans p2 (trans p3 (trans p4 p5)))

-- Equality up to a background-independent additive normalisation is therefore
-- enough to identify vacuum-subtracted quantities.
vacuumDifferenceRespectsConstantShift :
  {Background : Set} →
  (left right : Background → ℝ) →
  (constant : ℝ) →
  (shift : ∀ B → left B ≡ right B +ℝ constant) →
  ∀ background vacuum →
  vacuumDifference left background vacuum
    ≡ vacuumDifference right background vacuum
vacuumDifferenceRespectsConstantShift =
  backgroundIndependentTermCancels
