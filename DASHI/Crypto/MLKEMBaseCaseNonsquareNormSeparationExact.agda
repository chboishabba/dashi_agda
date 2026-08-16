module DASHI.Crypto.MLKEMBaseCaseNonsquareNormSeparationExact where

------------------------------------------------------------------------
-- ML-KEM BASECASE: NONSQUARE GAMMA -> NONZERO QUADRATIC NORM
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- PURPOSE
--
-- Close the algebraic seam left by MLKEMBaseCaseNormInverseBridgeExact.
-- Over a commutative ring with field-like inversion of every nonzero scalar,
-- decidable zero, and 1 != 0, prove constructively that
--
--   gamma nonsquare
--   and (a0,a1) != (0,0)
--       imply
--   a0^2 - gamma*a1^2 != 0.
--
-- This is exactly the norm-separation statement needed to construct the
-- explicit BaseCase left inverse.  The proof splits only on a1 = 0.
--
--   * If a1 = 0, nonzeroness forces a0 != 0; norm zero would give a0^2=0,
--     contradicting invertibility of a0 and 1 != 0.
--   * If a1 != 0, norm zero and a1^{-1} exhibit
--         (a0/a1)^2 = gamma,
--     contradicting nonsquareness.
--
-- No concrete claim about the 128 FIPS gamma_i is made here; that is the next
-- finite-field instantiation layer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Maybe.Base using (nothing)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

import DASHI.Crypto.MLKEMBaseCaseAdjugateInverseExact as Adjugate
import DASHI.Crypto.MLKEMBaseCaseNormInverseBridgeExact as NormBridge

record NormSeparationFieldLaws {c ℓ : Level}
  (R : CommutativeRing c ℓ) : Set (c Agda.Primitive.⊔ ℓ) where
  open CommutativeRing R
    renaming
      ( Carrier to F
      ; 0# to 0F
      ; 1# to 1F
      )
  field
    inverseSupplier : NormBridge.NonzeroInverseSupplier R
    zeroDecision : (x : F) → Dec (x ≡ 0F)
    oneNonzero : 1F ≡ 0F → ⊥

open NormSeparationFieldLaws public

module _ {c ℓ : Level}
  (R : CommutativeRing c ℓ)
  (laws : NormSeparationFieldLaws R)
  where

  open CommutativeRing R
    renaming
      ( Carrier to F
      ; _+_ to _⊕_
      ; _*_ to _⊗_
      ; -_ to neg
      ; 0# to 0F
      ; 1# to 1F
      )

  private
    solverRing : RingCore.AlmostCommutativeRing c ℓ
    solverRing = RingCore.fromCommutativeRing R (λ _ → nothing)

    module S = RingSolver solverRing

  Pair : Set c
  Pair = F × F

  Nonsquare : F → Set c
  Nonsquare gamma = (x : F) → (x ⊗ x ≡ gamma → ⊥)

  nonzeroPair : Pair → Set c
  nonzeroPair (a0 , a1) = a0 ≡ 0F → a1 ≡ 0F → ⊥

  private
    inverseOf : F → F
    inverseOf = NormBridge.inverseOf (inverseSupplier laws)

    inverseLaw :
      (x : F) →
      (x ≡ 0F → ⊥) →
      inverseOf x ⊗ x ≡ 1F
    inverseLaw = NormBridge.inverseLaw (inverseSupplier laws)

    squareZeroContradictsNonzero :
      (x : F) →
      (x ≡ 0F → ⊥) →
      x ⊗ x ≡ 0F →
      ⊥
    squareZeroContradictsNonzero x xNonzero squareZero =
      oneNonzero laws
        (S.solve 3
          (λ inv x one →
            (inv S.⊗ inv) S.⊗ (x S.⊗ x) S.⊜ one)
          squareZero
          (inverseLaw x xNonzero)
          (inverseLaw x xNonzero)
          (inverseOf x) x 1F)

    quotientSquareFromNormZero :
      (gamma a0 a1 : F) →
      (a1 ≡ 0F → ⊥) →
      Adjugate.normDelta R gamma (a0 , a1) ≡ 0F →
      (a0 ⊗ inverseOf a1) ⊗ (a0 ⊗ inverseOf a1) ≡ gamma
    quotientSquareFromNormZero gamma a0 a1 a1Nonzero normZero =
      S.solve 5
        (λ gamma a0 a1 inv one →
          (a0 S.⊗ inv) S.⊗ (a0 S.⊗ inv) S.⊜ gamma)
        normZero
        (inverseLaw a1 a1Nonzero)
        gamma a0 a1 (inverseOf a1) 1F

  nonsquareSeparatesNorm :
    (gamma : F) →
    Nonsquare gamma →
    (a : Pair) →
    nonzeroPair a →
    Adjugate.normDelta R gamma a ≡ 0F →
    ⊥
  nonsquareSeparatesNorm gamma gammaNonsquare (a0 , a1) pairNonzero normZero
    with zeroDecision laws a1
  ... | yes a1Zero =
    let
      a0Nonzero : a0 ≡ 0F → ⊥
      a0Nonzero a0Zero = pairNonzero a0Zero a1Zero

      squareZero : a0 ⊗ a0 ≡ 0F
      squareZero =
        S.solve 3
          (λ gamma a0 a1 → a0 S.⊗ a0 S.⊜ S.con 0)
          normZero
          a1Zero
          gamma a0 a1
    in squareZeroContradictsNonzero a0 a0Nonzero squareZero
  ... | no a1Nonzero =
    gammaNonsquare
      (a0 ⊗ inverseOf a1)
      (quotientSquareFromNormZero gamma a0 a1 a1Nonzero normZero)

  nonsquareQuadraticNormSeparated :
    (gamma : F) →
    Nonsquare gamma →
    (a : Pair) →
    nonzeroPair a →
    NormBridge.QuadraticNormSeparated R (inverseSupplier laws) gamma a
  nonsquareQuadraticNormSeparated gamma gammaNonsquare a aNonzero =
    NormBridge.quadratic-norm-separated
      (nonsquareSeparatesNorm gamma gammaNonsquare a aNonzero)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- Remaining source-specific producer:
--   instantiate R with F_3329 and prove, for every actual FIPS quadratic
--   constant gamma_i, Nonsquare gamma_i.
--
-- Once that is available, this file plus MLKEMBaseCaseNormInverseBridgeExact
-- mechanically produces the explicit left inverse consumed by the local
-- regular/singular outcome classifier.
------------------------------------------------------------------------
