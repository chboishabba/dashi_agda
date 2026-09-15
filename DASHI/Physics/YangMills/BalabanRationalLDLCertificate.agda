module DASHI.Physics.YangMills.BalabanRationalLDLCertificate where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import Data.Sum.Base using (inj₁; inj₂)
import Data.Rational.Tactic.RingSolver as ℚRing

sq : ℚ → ℚ
sq x = x * x

negSquare : ∀ q → (- q) * (- q) ≡ q * q
negSquare = ℚRing.solve-∀

negZero : - 0ℚ ≡ 0ℚ
negZero = ℚRing.solve-∀

squareNonnegative : ∀ q → 0ℚ ≤ sq q
squareNonnegative q with ℚP.≤-total 0ℚ q
... | inj₁ zero≤q =
  let
    instance
      qNonnegative : NonNegative q
      qNonnegative = nonNegative zero≤q
      qqNonnegative : NonNegative (q * q)
      qqNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg q q
  in ℚP.nonNegative⁻¹ (q * q)
... | inj₂ q≤zero =
  subst (λ value → 0ℚ ≤ value) (negSquare q)
    (let
      zero≤negqRaw = ℚP.neg-antimono-≤ q≤zero
      zero≤negq : 0ℚ ≤ - q
      zero≤negq = subst (λ value → value ≤ - q) negZero zero≤negqRaw
      instance
        negqNonnegative : NonNegative (- q)
        negqNonnegative = nonNegative zero≤negq
        negqSquaredNonnegative : NonNegative ((- q) * (- q))
        negqSquaredNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg (- q) (- q)
     in ℚP.nonNegative⁻¹ ((- q) * (- q)))

baseBelowBasePlusRemainder : ∀ base remainder →
  0ℚ ≤ remainder →
  base ≤ base + remainder
baseBelowBasePlusRemainder base remainder zero≤remainder =
  subst (λ value → value ≤ base + remainder)
    (ℚP.+-identityʳ base)
    (ℚP.+-mono-≤ (ℚP.≤-refl {x = base}) zero≤remainder)

------------------------------------------------------------------------
-- Generic exact LDL^T certificate consumer over rational coordinates.
--
-- A generated LDL decomposition is consumed as a finite list
--
--   d_j * (ell_j x)^2
--
-- with an exact polynomial reconstruction of the constrained quadratic form.
-- The theorem below is independent of the path length and therefore consumes
-- certificates emitted for any finite side L without trusting floating point
-- eigenvalues or a certificate generator at theorem-use time.
------------------------------------------------------------------------

record LDLTerm (Coordinate : Set) : Set where
  constructor ldlTerm
  field
    pivot : ℚ
    linearForm : Coordinate → ℚ
    pivotNonnegative : 0ℚ ≤ pivot

open LDLTerm public

termValue : ∀ {Coordinate} → LDLTerm Coordinate → Coordinate → ℚ
termValue term coordinate =
  pivot term * sq (linearForm term coordinate)

termValueNonnegative :
  ∀ {Coordinate} (term : LDLTerm Coordinate) coordinate →
  0ℚ ≤ termValue term coordinate
termValueNonnegative term coordinate =
  let
    instance
      pivotNonnegativeInstance : NonNegative (pivot term)
      pivotNonnegativeInstance = nonNegative (pivotNonnegative term)

      squareNonnegativeInstance :
        NonNegative (sq (linearForm term coordinate))
      squareNonnegativeInstance =
        nonNegative (squareNonnegative (linearForm term coordinate))

      productNonnegative :
        NonNegative (pivot term * sq (linearForm term coordinate))
      productNonnegative =
        ℚP.nonNeg*nonNeg⇒nonNeg
          (pivot term)
          (sq (linearForm term coordinate))
  in
  ℚP.nonNegative⁻¹
    (pivot term * sq (linearForm term coordinate))

sumTermValues :
  ∀ {Coordinate} → List (LDLTerm Coordinate) → Coordinate → ℚ
sumTermValues [] coordinate = 0ℚ
sumTermValues (term ∷ rest) coordinate =
  termValue term coordinate + sumTermValues rest coordinate

sumTermValuesNonnegative :
  ∀ {Coordinate} (terms : List (LDLTerm Coordinate)) coordinate →
  0ℚ ≤ sumTermValues terms coordinate
sumTermValuesNonnegative [] coordinate = ℚP.≤-refl
sumTermValuesNonnegative (term ∷ rest) coordinate =
  subst
    (λ value → value ≤
      termValue term coordinate + sumTermValues rest coordinate)
    (ℚP.+-identityˡ 0ℚ)
    (ℚP.+-mono-≤
      (termValueNonnegative term coordinate)
      (sumTermValuesNonnegative rest coordinate))

record RationalLDLCertificate (Coordinate : Set) : Set₁ where
  field
    normSq energy : Coordinate → ℚ
    coercivityConstant : ℚ
    terms : List (LDLTerm Coordinate)
    decomposition : ∀ coordinate →
      energy coordinate
      ≡ coercivityConstant * normSq coordinate
        + sumTermValues terms coordinate

open RationalLDLCertificate public

ldlCertificatePoincare :
  ∀ {Coordinate} (certificate : RationalLDLCertificate Coordinate) coordinate →
  coercivityConstant certificate * normSq certificate coordinate
  ≤ energy certificate coordinate
ldlCertificatePoincare certificate coordinate =
  subst
    (λ right →
      coercivityConstant certificate * normSq certificate coordinate
      ≤ right)
    (sym (decomposition certificate coordinate))
    (baseBelowBasePlusRemainder
      (coercivityConstant certificate * normSq certificate coordinate)
      (sumTermValues (terms certificate) coordinate)
      (sumTermValuesNonnegative (terms certificate) coordinate))

arbitraryLengthLDLCertificateConsumerLevel : ProofLevel
arbitraryLengthLDLCertificateConsumerLevel = machineChecked

arbitraryLengthGeneratedCertificateInputLevel : ProofLevel
arbitraryLengthGeneratedCertificateInputLevel = computed
