module DASHI.Analysis.RiemannG21AugmentedDeterminantFiniteExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite exact witness for the algebraic mechanism behind G21.
--
-- A signed determinant over Nat is represented by two nonnegative sums
-- (positive permutation monomials, negative permutation monomials).  Two
-- codes represent the same signed integer when cross-addition agrees:
--
--   pos(A) + neg(B) = neg(A) + pos(B).
--
-- This avoids pretending Nat itself has subtraction while still allowing an
-- exact finite regression of the row-addition/pole-quotient mechanism.
------------------------------------------------------------------------

Vec3 : Set
Vec3 = Nat × (Nat × Nat)

record OrientedDet3Code : Set where
  constructor det3Code
  field
    positiveSum : Nat
    negativeSum : Nat

open OrientedDet3Code public

det3 : Vec3 → Vec3 → Vec3 → OrientedDet3Code
det3
  (a₁ , (a₂ , a₃))
  (b₁ , (b₂ , b₃))
  (c₁ , (c₂ , c₃)) =
  det3Code
    (a₁ * b₂ * c₃ + a₂ * b₃ * c₁ + a₃ * b₁ * c₂)
    (a₃ * b₂ * c₁ + a₂ * b₁ * c₃ + a₁ * b₃ * c₂)

SameSignedDeterminant : OrientedDet3Code → OrientedDet3Code → Set
SameSignedDeterminant left right =
  positiveSum left + negativeSum right
  ≡
  negativeSum left + positiveSum right

_+v3_ : Vec3 → Vec3 → Vec3
(a₁ , (a₂ , a₃)) +v3 (b₁ , (b₂ , b₃)) =
  (a₁ + b₁ , (a₂ + b₂ , a₃ + b₃))

poleProfile : Vec3
poleProfile = 1 , (1 , 1)

residual₁ residual₂ : Vec3
residual₁ = 1 , (0 , 0)
residual₂ = 0 , (1 , 0)

response₁ response₂ : Vec3
response₁ = residual₁ +v3 poleProfile
response₂ = residual₂ +v3 poleProfile

residualDeterminantCode :
  det3 residual₁ residual₂ poleProfile ≡ det3Code 1 0
residualDeterminantCode = refl

responseDeterminantCode :
  det3 response₁ response₂ poleProfile ≡ det3Code 6 5
responseDeterminantCode = refl

augmentedPoleQuotientPreservesSignedDeterminant :
  SameSignedDeterminant
    (det3 response₁ response₂ poleProfile)
    (det3 residual₁ residual₂ poleProfile)
augmentedPoleQuotientPreservesSignedDeterminant = refl

responseAndResidualCodesAreNotSyntacticallyEqual :
  det3 response₁ response₂ poleProfile
  ≡ det3 residual₁ residual₂ poleProfile
  → ⊥
responseAndResidualCodesAreNotSyntacticallyEqual ()

record AugmentedDeterminantFiniteBoundary : Set where
  constructor augmentedDeterminantFiniteBoundary
  field
    finitePoleQuotientMechanismWitnessed : Bool
    finitePoleQuotientMechanismWitnessedIsTrue :
      finitePoleQuotientMechanismWitnessed ≡ true

    positiveNegativeMonomialListsStayIdentical : Bool
    positiveNegativeMonomialListsStayIdenticalIsFalse :
      positiveNegativeMonomialListsStayIdentical ≡ false

    finiteWitnessProvesLiteralWeilIdentity : Bool
    finiteWitnessProvesLiteralWeilIdentityIsFalse :
      finiteWitnessProvesLiteralWeilIdentity ≡ false

canonicalAugmentedDeterminantFiniteBoundary :
  AugmentedDeterminantFiniteBoundary
canonicalAugmentedDeterminantFiniteBoundary =
  augmentedDeterminantFiniteBoundary
    true refl
    false refl
    false refl
