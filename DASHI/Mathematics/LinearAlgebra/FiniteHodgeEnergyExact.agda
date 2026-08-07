module DASHI.Mathematics.LinearAlgebra.FiniteHodgeEnergyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jozef Dodziuk,
-- "Finite-Difference Approach to the Hodge Theory of Harmonic Forms",
-- American Journal of Mathematics 98 (1976), 79--104.
-- DOI: 10.2307/2373615.
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- DASHI CONTRIBUTION
--
-- A finite rational cochain/Hodge energy theorem.  From supplied adjointness,
-- inner-product symmetry and positivity data, the degree-one Laplacian
--
--   Delta = d0 d0* + d1* d1
--
-- satisfies
--
--   <Delta x,x> = <d0* x,d0* x> + <d1 x,d1 x>.
--
-- Consequently a harmonic cochain is simultaneously closed and coclosed.
-- The proof is algebraic and reusable by the finite Maxwell, Yang--Mills,
-- topology and spectral lanes; it does not assume analytic elliptic
-- regularity or a continuum Hodge theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)

symmetry : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symmetry refl = refl

transitivity : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transitivity refl second = second

congruence : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
congruence f refl = refl

congruence₂ : ∀ {A B C : Set} (f : A → B → C)
  {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
congruence₂ f refl refl = refl

record RationalHodgeEnergyComplex : Set₁ where
  field
    C0 C1 C2 : Set

    zero0 : C0
    zero1 : C1
    zero2 : C2
    add1 : C1 → C1 → C1

    d0 : C0 → C1
    d1 : C1 → C2
    d0Adjoint : C1 → C0
    d1Adjoint : C2 → C1

    inner0 : C0 → C0 → ℚ
    inner1 : C1 → C1 → ℚ
    inner2 : C2 → C2 → ℚ

    dSquaredZero : ∀ x → d1 (d0 x) ≡ zero2
    inner1AdditiveLeft : ∀ x y z →
      inner1 (add1 x y) z ≡ inner1 x z + inner1 y z
    inner1Symmetric : ∀ x y → inner1 x y ≡ inner1 y x
    inner1ZeroLeft : ∀ x → inner1 zero1 x ≡ 0ℚ

    d0AdjointLaw : ∀ x y →
      inner1 (d0 x) y ≡ inner0 x (d0Adjoint y)
    d1AdjointLaw : ∀ x y →
      inner2 (d1 x) y ≡ inner1 x (d1Adjoint y)

    sumNormsZeroImpliesBothZero : ∀ x y →
      inner0 x x + inner2 y y ≡ 0ℚ →
      x ≡ zero0 × y ≡ zero2

open RationalHodgeEnergyComplex public

hodgeLaplacian :
  (complex : RationalHodgeEnergyComplex) → C1 complex → C1 complex
hodgeLaplacian complex x =
  add1 complex
    (d0 complex (d0Adjoint complex x))
    (d1Adjoint complex (d1 complex x))

hodgeEnergyIdentity :
  ∀ complex x →
  inner1 complex (hodgeLaplacian complex x) x
  ≡ inner0 complex (d0Adjoint complex x) (d0Adjoint complex x)
    + inner2 complex (d1 complex x) (d1 complex x)
hodgeEnergyIdentity complex x =
  transitivity
    (inner1AdditiveLeft complex
      (d0 complex (d0Adjoint complex x))
      (d1Adjoint complex (d1 complex x))
      x)
    (congruence₂ _+_
      (d0AdjointLaw complex (d0Adjoint complex x) x)
      (transitivity
        (inner1Symmetric complex
          (d1Adjoint complex (d1 complex x)) x)
        (symmetry
          (d1AdjointLaw complex x (d1 complex x)))))

Harmonic1 :
  (complex : RationalHodgeEnergyComplex) → C1 complex → Set
Harmonic1 complex x = hodgeLaplacian complex x ≡ zero1 complex

Closed1 :
  (complex : RationalHodgeEnergyComplex) → C1 complex → Set
Closed1 complex x = d1 complex x ≡ zero2 complex

Coclosed1 :
  (complex : RationalHodgeEnergyComplex) → C1 complex → Set
Coclosed1 complex x = d0Adjoint complex x ≡ zero0 complex

harmonicEnergyIsZero :
  ∀ complex x → Harmonic1 complex x →
  inner0 complex (d0Adjoint complex x) (d0Adjoint complex x)
    + inner2 complex (d1 complex x) (d1 complex x)
  ≡ 0ℚ
harmonicEnergyIsZero complex x harmonic =
  transitivity
    (symmetry (hodgeEnergyIdentity complex x))
    (transitivity
      (congruence (λ operatorValue → inner1 complex operatorValue x) harmonic)
      (inner1ZeroLeft complex x))

harmonicImpliesCoclosedAndClosed :
  ∀ complex x → Harmonic1 complex x →
  Coclosed1 complex x × Closed1 complex x
harmonicImpliesCoclosedAndClosed complex x harmonic =
  sumNormsZeroImpliesBothZero complex
    (d0Adjoint complex x)
    (d1 complex x)
    (harmonicEnergyIsZero complex x harmonic)

harmonicImpliesClosed :
  ∀ complex x → Harmonic1 complex x → Closed1 complex x
harmonicImpliesClosed complex x harmonic =
  proj₂ (harmonicImpliesCoclosedAndClosed complex x harmonic)

harmonicImpliesCoclosed :
  ∀ complex x → Harmonic1 complex x → Coclosed1 complex x
harmonicImpliesCoclosed complex x harmonic =
  proj₁ (harmonicImpliesCoclosedAndClosed complex x harmonic)
