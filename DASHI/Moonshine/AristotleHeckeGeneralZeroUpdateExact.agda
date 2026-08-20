module DASHI.Moonshine.AristotleHeckeGeneralZeroUpdateExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.HeckeGeneral
--   SHA-256 a45235046a9f46c7fb0b8c86282db5be52f8637ee309096e0dfbc0b4b013c2cf
--
-- Source theorem: Hecke23.a_zero_undetermined.
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
--
-- Toshitsune Miyake, "Modular Forms", Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Port the exact algebraic content of Aristotle's `a_zero_undetermined` to the
-- existing recurrence core.  The source works over a CommRing, so the one extra
-- structure needed beyond RecurrenceCoefficientAlgebra is the multiplicative
-- unit law.  Updating a coefficient function only at index zero preserves:
--
--   * a(1) = 1;
--   * coprime multiplicativity, including the 0-coprime boundary where the
--     other factor is forced to be 1;
--   * every prime-power recurrence, because prime powers are nonzero.
--
-- Hence the positive Hecke data cannot determine a(0).  This is a theorem, not
-- a boundary flag.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_^_; ≢-nonZero⁻¹)
open import Data.Nat.Coprimality using (Coprime; 0-coprimeTo-m⇒m≡1)
import Data.Nat.Coprimality as Coprime
open import Data.Nat.Primality using (Prime; prime⇒nonZero)
open import Data.Nat.Properties using (m*n≢0; m^n≢0)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; cong₂; sym; trans)

import DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact as Recurrence
import DASHI.Moonshine.AristotleHeckeGeneralPrimePowerDecompositionExact as General

------------------------------------------------------------------------
-- The minimal unit laws supplied automatically by Aristotle's CommRing.
------------------------------------------------------------------------

record UnitalRecurrenceAlgebra
    (A : Recurrence.RecurrenceCoefficientAlgebra) : Set₁ where
  field
    mulOneLeft :
      (x : Recurrence.Carrier A) →
      Recurrence.mul A (Recurrence.one A) x ≡ x
    mulOneRight :
      (x : Recurrence.Carrier A) →
      Recurrence.mul A x (Recurrence.one A) ≡ x

open UnitalRecurrenceAlgebra public

------------------------------------------------------------------------
-- Constructive update at exactly index zero.
------------------------------------------------------------------------

updateZero :
  {A : Set} →
  (Nat → A) → A → Nat → A
updateZero f c zero = c
updateZero f c (suc n) = f (suc n)

updateZeroAwayFromZero :
  {A : Set} →
  (f : Nat → A) →
  (c : A) →
  {n : Nat} →
  n ≢ zero →
  updateZero f c n ≡ f n
updateZeroAwayFromZero f c {zero} n≢0 = ⊥-elim (n≢0 refl)
updateZeroAwayFromZero f c {suc n} n≢0 = refl

primePowerAwayFromZero :
  {A : Set} →
  (f : Nat → A) →
  (c : A) →
  (p exponent : Nat) →
  Prime p →
  updateZero f c (p ^ exponent) ≡ f (p ^ exponent)
primePowerAwayFromZero f c p exponent primeP =
  updateZeroAwayFromZero f c
    (≢-nonZero⁻¹ (p ^ exponent)
      {{m^n≢0 p exponent {{prime⇒nonZero primeP}}}})

------------------------------------------------------------------------
-- Updating zero preserves the complete positive Hecke closure system.
------------------------------------------------------------------------

zeroUpdatePreservesHeckeSystem :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  UnitalRecurrenceAlgebra A →
  (scale : Nat → Recurrence.Carrier A) →
  (coefficient : Nat → Recurrence.Carrier A) →
  General.NatHeckeClosureSystem A scale coefficient →
  (c : Recurrence.Carrier A) →
  General.NatHeckeClosureSystem A scale (updateZero coefficient c)
zeroUpdatePreservesHeckeSystem A unit scale coefficient hecke c =
  record
    { normalisedOne =
        trans
          (updateZeroAwayFromZero coefficient c (λ ()))
          (General.normalisedOne hecke)
    ; coprimeMultiplicative = updatedCoprime
    ; primePowerLane = updatedPrimePowerLane
    }
  where
  updatedCoprime :
    (m n : Nat) →
    Coprime m n →
    updateZero coefficient c (m * n)
    ≡ Recurrence.mul A (updateZero coefficient c m) (updateZero coefficient c n)
  updatedCoprime zero n cop
    rewrite 0-coprimeTo-m⇒m≡1 cop =
      sym
        (trans
          (cong (Recurrence.mul A c) (General.normalisedOne hecke))
          (mulOneRight unit c))
  updatedCoprime (suc m) zero cop
    rewrite 0-coprimeTo-m⇒m≡1 (Coprime.sym cop) =
      sym
        (trans
          (cong (λ x → Recurrence.mul A x c) (General.normalisedOne hecke))
          (mulOneLeft unit c))
  updatedCoprime (suc m) (suc n) cop =
    trans
      (updateZeroAwayFromZero coefficient c
        (≢-nonZero⁻¹ ((suc m) * (suc n))
          {{m*n≢0 (suc m) (suc n)}}))
      (General.coprimeMultiplicative hecke (suc m) (suc n) cop)

  updatedPrimePowerLane :
    (p : Nat) →
    Prime p →
    Recurrence.PrimePowerHeckeSystem
      A (scale p) (λ exponent → updateZero coefficient c (p ^ exponent))
  updatedPrimePowerLane p primeP =
    record
      { normalised =
          trans
            (primePowerAwayFromZero coefficient c p zero primeP)
            (Recurrence.normalised (General.primePowerLane hecke p primeP))
      ; primePowerRecurrence = λ n →
          trans
            (primePowerAwayFromZero coefficient c p (suc (suc n)) primeP)
            (trans
              (Recurrence.primePowerRecurrence
                (General.primePowerLane hecke p primeP) n)
              (sym
                (cong₂ (Recurrence.sub A)
                  (cong₂ (Recurrence.mul A)
                    (primePowerAwayFromZero coefficient c p (suc zero) primeP)
                    (primePowerAwayFromZero coefficient c p (suc n) primeP))
                  (cong₂ (Recurrence.mul A)
                    refl
                    (primePowerAwayFromZero coefficient c p n primeP)))))
      }

------------------------------------------------------------------------
-- Source conclusion: every positive coefficient is unchanged.
------------------------------------------------------------------------

aZeroUndetermined :
  (A : Recurrence.RecurrenceCoefficientAlgebra) →
  (unit : UnitalRecurrenceAlgebra A) →
  (scale : Nat → Recurrence.Carrier A) →
  (coefficient : Nat → Recurrence.Carrier A) →
  (hecke : General.NatHeckeClosureSystem A scale coefficient) →
  (c : Recurrence.Carrier A) →
  General.NatHeckeClosureSystem A scale (updateZero coefficient c)
  ×
  ((n : Nat) → n ≢ zero → updateZero coefficient c n ≡ coefficient n)
aZeroUndetermined A unit scale coefficient hecke c =
  zeroUpdatePreservesHeckeSystem A unit scale coefficient hecke c ,
  λ n n≢0 → updateZeroAwayFromZero coefficient c n≢0

record AristotleHeckeGeneralZeroBoundary : Set where
  field
    arbitraryZeroUpdatePreservesPositiveHeckeAxioms : Bool
    arbitraryZeroUpdatePreservesPositiveHeckeAxiomsIsTrue :
      arbitraryZeroUpdatePreservesPositiveHeckeAxioms ≡ true
    positiveCoefficientsUnaffected : Bool
    positiveCoefficientsUnaffectedIsTrue :
      positiveCoefficientsUnaffected ≡ true

canonicalAristotleHeckeGeneralZeroBoundary : AristotleHeckeGeneralZeroBoundary
canonicalAristotleHeckeGeneralZeroBoundary = record
  { arbitraryZeroUpdatePreservesPositiveHeckeAxioms = true
  ; arbitraryZeroUpdatePreservesPositiveHeckeAxiomsIsTrue = refl
  ; positiveCoefficientsUnaffected = true
  ; positiveCoefficientsUnaffectedIsTrue = refl
  }
