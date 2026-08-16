module DASHI.Crypto.MLKEMBaseCaseNormInverseBridgeExact where

------------------------------------------------------------------------
-- ML-KEM BASECASE: NONZERO NORM -> EXPLICIT LEFT INVERSE
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This module isolates the final field-theoretic seam beneath the explicit
-- adjugate calculation.  MLKEMBaseCaseAdjugateInverseExact already proves
--
--   adj(a) M(a) = Delta(a) I.
--
-- Therefore, once the scalar carrier supplies an inverse for every nonzero
-- element and Delta(a) is known nonzero, BaseCase multiplication has an
-- explicit LeftInverseAtZero witness.
--
-- The remaining FIPS-specific arithmetic problem is now exactly:
--
--   gamma_i nonsquare and a != 0
--      -> a0^2 - gamma_i a1^2 != 0
--
-- in F_3329.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.MLKEMBaseCaseAdjugateInverseExact as Adjugate
open import DASHI.Crypto.MLKEMNTTLocalLeftInverseZeroReflectionExact using
  ( LeftInverseAtZero )

record NonzeroInverseSupplier {c ℓ : Level}
  (R : CommutativeRing c ℓ) : Set (c Agda.Primitive.⊔ ℓ) where
  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _*_ to _⊗_
      ; 0# to 0F
      ; 1# to 1F
      )
  field
    inverseOf : F → F
    inverseLaw :
      (x : F) →
      (x ≡ 0F → ⊥) →
      inverseOf x ⊗ x ≡ 1F

open NonzeroInverseSupplier public

module _ {c ℓ : Level}
  (R : CommutativeRing c ℓ)
  (inverseSupplier : NonzeroInverseSupplier R)
  where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; 0# to 0F
      )

  Pair : Set c
  Pair = F × F

  nonzeroPair : Pair → Set
  nonzeroPair (a0 , a1) = (a0 ≡ 0F → a1 ≡ 0F → ⊥)

  record QuadraticNormSeparated (gamma : F) (a : Pair) : Set (c Agda.Primitive.⊔ ℓ) where
    constructor quadratic-norm-separated
    field
      normNonzero :
        Adjugate.normDelta R gamma a ≡ 0F → ⊥

  open QuadraticNormSeparated public

  normSeparatedBaseCaseLeftInverse :
    (gamma : F) →
    (a : Pair) →
    QuadraticNormSeparated gamma a →
    LeftInverseAtZero Pair Pair
  normSeparatedBaseCaseLeftInverse gamma a separation =
    Adjugate.baseCaseLeftInverseAtZero R
      gamma
      a
      (inverseOf inverseSupplier (Adjugate.normDelta R gamma a))
      (inverseLaw inverseSupplier
        (Adjugate.normDelta R gamma a)
        (normNonzero separation))
