module DASHI.Physics.YangMills.BalabanRationalLDLCertificate where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; squareNonnegative; baseBelowBasePlusRemainder)

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
