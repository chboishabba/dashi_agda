module DASHI.Analysis.RiemannAristotleDeterminantCovarianceCompilerExact where

------------------------------------------------------------------------
-- G2 / ONE-DIMENSIONAL SCHUR QUOTIENT COMPILER
--
-- Three taper coordinates minus two independent nuisance directions leave a
-- one-dimensional quotient.  Lean already uses the 3x3 determinant as the exact
-- survival criterion for `elim2`; however this Agda return does NOT claim that
-- the bilinear determinant formula below is already proved in Lean.
--
-- This compiler isolates the single exact source theorem which would make the
-- one-dimensional structure quantitative:
--
--   <E x, E y>
--     = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2).
--
-- Once supplied, every finite Gram cross term becomes a signed PRODUCT OF TWO
-- SCALARS.  The difficult RH estimate is then a finite oscillatory covariance
-- for determinant responses, not a vector/matrix norm estimate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)

record DeterminantCovarianceSurface : Set₁ where
  constructor determinant-covariance-surface
  field
    Scalar : Set
    Cell : Set

    zero : Scalar
    add multiply divide : Scalar → Scalar → Scalar

    postSchurDot : Cell → Cell → Scalar
    determinantResponse : Cell → Scalar
    nuisanceWedgeSq : Scalar

    postSchurDotIsDeterminantProduct : ∀ x y →
      postSchurDot x y
      ≡ divide
          (multiply (determinantResponse x) (determinantResponse y))
          nuisanceWedgeSq

open DeterminantCovarianceSurface public

sumAgainst :
  (S : DeterminantCovarianceSurface) →
  (x : Cell S) → List (Cell S) → Scalar S
sumAgainst S x [] = zero S
sumAgainst S x (y ∷ ys) =
  add S (postSchurDot S x y) (sumAgainst S x ys)

unorderedSchurCovariance :
  (S : DeterminantCovarianceSurface) →
  List (Cell S) → Scalar S
unorderedSchurCovariance S [] = zero S
unorderedSchurCovariance S (x ∷ xs) =
  add S (sumAgainst S x xs) (unorderedSchurCovariance S xs)

determinantPairTerm :
  (S : DeterminantCovarianceSurface) →
  Cell S → Cell S → Scalar S
determinantPairTerm S x y =
  divide S
    (multiply S
      (determinantResponse S x)
      (determinantResponse S y))
    (nuisanceWedgeSq S)

determinantSumAgainst :
  (S : DeterminantCovarianceSurface) →
  (x : Cell S) → List (Cell S) → Scalar S
determinantSumAgainst S x [] = zero S
determinantSumAgainst S x (y ∷ ys) =
  add S (determinantPairTerm S x y) (determinantSumAgainst S x ys)

unorderedDeterminantCovariance :
  (S : DeterminantCovarianceSurface) →
  List (Cell S) → Scalar S
unorderedDeterminantCovariance S [] = zero S
unorderedDeterminantCovariance S (x ∷ xs) =
  add S
    (determinantSumAgainst S x xs)
    (unorderedDeterminantCovariance S xs)

sumAgainstIsDeterminantSum :
  (S : DeterminantCovarianceSurface) →
  (x : Cell S) →
  (xs : List (Cell S)) →
  sumAgainst S x xs ≡ determinantSumAgainst S x xs
sumAgainstIsDeterminantSum S x [] = refl
sumAgainstIsDeterminantSum S x (y ∷ ys)
  rewrite postSchurDotIsDeterminantProduct S x y
        | sumAgainstIsDeterminantSum S x ys = refl

schurCovarianceIsDeterminantCovariance :
  (S : DeterminantCovarianceSurface) →
  (cells : List (Cell S)) →
  unorderedSchurCovariance S cells
  ≡ unorderedDeterminantCovariance S cells
schurCovarianceIsDeterminantCovariance S [] = refl
schurCovarianceIsDeterminantCovariance S (x ∷ xs)
  rewrite sumAgainstIsDeterminantSum S x xs
        | schurCovarianceIsDeterminantCovariance S xs = refl

record DeterminantCovarianceBoundary : Set where
  constructor determinant-covariance-boundary
  field
    determinantScalarizationCompilerClosedInAgda : Bool
    determinantScalarizationCompilerClosedInAgdaIsTrue :
      determinantScalarizationCompilerClosedInAgda ≡ true

    literalLeanBilinearDeterminantIdentitySupplied : Bool
    literalLeanBilinearDeterminantIdentitySuppliedIsFalse :
      literalLeanBilinearDeterminantIdentitySupplied ≡ false

    finiteSignedDeterminantCovarianceEstimateClosed : Bool
    finiteSignedDeterminantCovarianceEstimateClosedIsFalse :
      finiteSignedDeterminantCovarianceEstimateClosed ≡ false

canonicalDeterminantCovarianceBoundary : DeterminantCovarianceBoundary
canonicalDeterminantCovarianceBoundary =
  determinant-covariance-boundary true refl false refl false refl
