module DASHI.Analysis.NonArchimedeanCharacteristicRootUnionCompilerExact where

------------------------------------------------------------------------
-- CHARACTERISTIC-ROOT UNION COMPILER
--
-- For a finite block decomposition, once the characteristic determinant
-- factorization is available
--
--   chi_D(lambda) = chi_W(lambda) * chi_S(lambda),
--
-- root membership in chi_D is exactly the union of root membership in the two
-- factors, provided the scalar carrier has no zero divisors.  This is the
-- correct finite-spectrum consumer shape; it does not use an `Eigenpair`
-- record that permits the zero vector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

record ZeroProductScalar (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    multiply : Scalar → Scalar → Scalar
    zeroProductCases :
      (a b : Scalar) → multiply a b ≡ zero → (a ≡ zero) ⊎ (b ≡ zero)
    zeroLeft : (a : Scalar) → multiply zero a ≡ zero
    zeroRight : (a : Scalar) → multiply a zero ≡ zero

open ZeroProductScalar public

record CharacteristicFactorization {Scalar : Set}
    (laws : ZeroProductScalar Scalar) : Set₁ where
  field
    Lambda : Set
    chiWhole chiLeft chiRight : Lambda → Scalar
    factorization :
      (lambda : Lambda) →
      chiWhole lambda ≡ multiply laws (chiLeft lambda) (chiRight lambda)

open CharacteristicFactorization public

WholeRoot LeftRoot RightRoot :
  ∀ {Scalar} (laws : ZeroProductScalar Scalar) →
  CharacteristicFactorization laws → Set
WholeRoot laws data =
  Σ (Lambda data) (λ lambda → chiWhole data lambda ≡ zero laws)
LeftRoot laws data =
  Σ (Lambda data) (λ lambda → chiLeft data lambda ≡ zero laws)
RightRoot laws data =
  Σ (Lambda data) (λ lambda → chiRight data lambda ≡ zero laws)

wholeRootSplits :
  ∀ {Scalar}
    (laws : ZeroProductScalar Scalar)
    (data : CharacteristicFactorization laws)
    (lambda : Lambda data) →
  chiWhole data lambda ≡ zero laws →
  (chiLeft data lambda ≡ zero laws) ⊎
  (chiRight data lambda ≡ zero laws)
wholeRootSplits laws data lambda hWhole =
  zeroProductCases laws
    (chiLeft data lambda)
    (chiRight data lambda)
    (trans (sym (factorization data lambda)) hWhole)

leftRootInjectsWhole :
  ∀ {Scalar}
    (laws : ZeroProductScalar Scalar)
    (data : CharacteristicFactorization laws)
    (lambda : Lambda data) →
  chiLeft data lambda ≡ zero laws →
  chiWhole data lambda ≡ zero laws
leftRootInjectsWhole laws data lambda hLeft =
  trans
    (factorization data lambda)
    (trans
      (cong (λ x → multiply laws x (chiRight data lambda)) hLeft)
      (zeroLeft laws (chiRight data lambda)))

rightRootInjectsWhole :
  ∀ {Scalar}
    (laws : ZeroProductScalar Scalar)
    (data : CharacteristicFactorization laws)
    (lambda : Lambda data) →
  chiRight data lambda ≡ zero laws →
  chiWhole data lambda ≡ zero laws
rightRootInjectsWhole laws data lambda hRight =
  trans
    (factorization data lambda)
    (trans
      (cong (multiply laws (chiLeft data lambda)) hRight)
      (zeroRight laws (chiLeft data lambda)))

record RootUnionBoundary : Set where
  constructor rootUnionBoundary
  field
    zeroVectorEigenpairShortcutAllowed : Bool
    fredholmRootUnionEqualsSpectrumWithoutReciprocalCheck : Bool
    characteristicFactorizationClosesFiniteRootUnion : Bool

canonicalRootUnionBoundary : RootUnionBoundary
canonicalRootUnionBoundary = rootUnionBoundary false false true
