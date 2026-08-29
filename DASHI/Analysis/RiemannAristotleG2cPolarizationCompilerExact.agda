module DASHI.Analysis.RiemannAristotleG2cPolarizationCompilerExact where

------------------------------------------------------------------------
-- G2c / EXACT POLARIZATION COMPILER
--
-- Lean already owns, on the literal Fin 3 Schur carrier,
--
--   normSqP (elim2 n1 n2 x)
--     = det3 n1 n2 x ^ 2 / wedgeSq n1 n2.
--
-- Together with additivity of elim2 and additivity of det3 in the third
-- argument, ordinary polarization yields
--
--   <E x,E y>
--     = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2).
--
-- This file isolates that implication abstractly.  It does not claim that the
-- corresponding new Lean theorem has already received a fresh kernel receipt.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

record PolarizedDeterminantSurface : Set₁ where
  constructor polarized-determinant-surface
  field
    Scalar Cell : Set
    zero : Scalar
    add multiply subtract divide : Scalar → Scalar → Scalar
    addCell : Cell → Cell → Cell
    dot : Cell → Cell → Scalar
    normSq determinant : Cell → Scalar
    wedgeSq : Scalar

    doubleCancel : ∀ a b →
      add a a ≡ add b b → a ≡ b

    polarization : ∀ x y →
      add (dot x y) (dot x y)
      ≡ subtract
          (subtract (normSq (addCell x y)) (normSq x))
          (normSq y)

    normSqIsDeterminantRatio : ∀ x →
      normSq x
      ≡ divide (multiply (determinant x) (determinant x)) wedgeSq

    determinantAdd : ∀ x y →
      determinant (addCell x y)
      ≡ add (determinant x) (determinant y)

    determinantRatioPolarizes : ∀ a b →
      subtract
        (subtract
          (divide (multiply (add a b) (add a b)) wedgeSq)
          (divide (multiply a a) wedgeSq))
        (divide (multiply b b) wedgeSq)
      ≡ add
          (divide (multiply a b) wedgeSq)
          (divide (multiply a b) wedgeSq)

open PolarizedDeterminantSurface public

postSchurDotIsDeterminantProduct :
  (S : PolarizedDeterminantSurface) →
  (x y : Cell S) →
  dot S x y
  ≡ divide S
      (multiply S (determinant S x) (determinant S y))
      (wedgeSq S)
postSchurDotIsDeterminantProduct S x y =
  doubleCancel S _ _
    (trans
      (polarization S x y)
      (trans
        (cong
          (λ q → subtract S (subtract S q (normSq S x)) (normSq S y))
          (trans
            (normSqIsDeterminantRatio S (addCell S x y))
            (cong
              (λ d → divide S (multiply S d d) (wedgeSq S))
              (determinantAdd S x y))))
        (trans
          (cong
            (λ q → subtract S q (normSq S y))
            (cong
              (subtract S
                (divide S
                  (multiply S
                    (add S (determinant S x) (determinant S y))
                    (add S (determinant S x) (determinant S y)))
                  (wedgeSq S)))
              (normSqIsDeterminantRatio S x)))
          (trans
            (cong
              (subtract S
                (subtract S
                  (divide S
                    (multiply S
                      (add S (determinant S x) (determinant S y))
                      (add S (determinant S x) (determinant S y)))
                    (wedgeSq S))
                  (divide S
                    (multiply S (determinant S x) (determinant S x))
                    (wedgeSq S))))
              (normSqIsDeterminantRatio S y))
            (determinantRatioPolarizes S (determinant S x) (determinant S y))))))

record G2cPolarizationBoundary : Set where
  constructor g2c-polarization-boundary
  field
    polarizationCompilerClosedInAgda : Bool
    polarizationCompilerClosedInAgdaIsTrue : polarizationCompilerClosedInAgda ≡ true

    checkedLeanNormDeterminantOwnerExists : Bool
    checkedLeanNormDeterminantOwnerExistsIsTrue : checkedLeanNormDeterminantOwnerExists ≡ true

    freshLiteralLeanBilinearTheoremKernelCheckedHere : Bool
    freshLiteralLeanBilinearTheoremKernelCheckedHereIsFalse :
      freshLiteralLeanBilinearTheoremKernelCheckedHere ≡ false

canonicalG2cPolarizationBoundary : G2cPolarizationBoundary
canonicalG2cPolarizationBoundary =
  g2c-polarization-boundary true refl true refl false refl
