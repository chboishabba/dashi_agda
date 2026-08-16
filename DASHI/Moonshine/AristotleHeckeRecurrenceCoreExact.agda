module DASHI.Moonshine.AristotleHeckeRecurrenceCoreExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source modules:
--   RequestProject.Hecke23
--   SHA-256 c433699f95c7f067c772fd9223e444869ba4e4e54907b37d4db34616572676bc
--   RequestProject.HeckeGeneral
--   SHA-256 a45235046a9f46c7fb0b8c86282db5be52f8637ee309096e0dfbc0b4b013c2cf
--
-- The upstream README requests @Aristotle-Harmonic attribution and the commit
-- trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCES / CONTEXT
-- Jean-Pierre Serre, "A Course in Arithmetic", GTM 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake, "Modular Forms", Springer Monographs in Mathematics,
-- Springer, 2006. DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
-- Isolate and construct the recurrence kernel of Aristotle's Hecke23 theorem
-- without assuming analytic modular forms.  At a fixed prime, normalisation
-- plus the second-order Hecke recurrence make the complete prime-power lane a
-- deterministic function of the first eigenvalue.  Two prime lanes agreeing
-- at exponent one therefore agree at every exponent.  Pairing the independent
-- 2- and 3-prime lanes gives the corresponding exact 3-smooth uniqueness core.
--
-- This is deliberately narrower than the source's full Nat HeckeSystem: the
-- coprime multiplicativity and arbitrary Nat prime-factorisation layer remains
-- separately tracked in the parity ledger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

record RecurrenceCoefficientAlgebra : Set₁ where
  field
    Carrier : Set
    one : Carrier
    mul : Carrier → Carrier → Carrier
    sub : Carrier → Carrier → Carrier

open RecurrenceCoefficientAlgebra public

record PrimePowerHeckeSystem
    (A : RecurrenceCoefficientAlgebra)
    (scale : Carrier A)
    (coeff : Nat → Carrier A) : Set where
  field
    normalised : coeff zero ≡ one A
    primePowerRecurrence :
      (n : Nat) →
      coeff (suc (suc n))
      ≡ sub A
          (mul A (coeff (suc zero)) (coeff (suc n)))
          (mul A scale (coeff n))

open PrimePowerHeckeSystem public

primePowerPairUniqueness :
  (A : RecurrenceCoefficientAlgebra) →
  (scale : Carrier A) →
  (a b : Nat → Carrier A) →
  PrimePowerHeckeSystem A scale a →
  PrimePowerHeckeSystem A scale b →
  a (suc zero) ≡ b (suc zero) →
  (n : Nat) →
  (a n ≡ b n) × (a (suc n) ≡ b (suc n))
primePowerPairUniqueness A scale a b ha hb firstAgreement zero =
  trans (normalised ha) (sym (normalised hb)) , firstAgreement
primePowerPairUniqueness A scale a b ha hb firstAgreement (suc n)
  with primePowerPairUniqueness A scale a b ha hb firstAgreement n
... | agreementN , agreementSucN =
  agreementSucN ,
  trans
    (primePowerRecurrence ha n)
    (trans
      (cong₂ (sub A)
        (cong₂ (mul A) firstAgreement agreementSucN)
        (cong₂ (mul A) refl agreementN))
      (sym (primePowerRecurrence hb n)))

primePowerDeterminedByPrimeEigenvalue :
  (A : RecurrenceCoefficientAlgebra) →
  (scale : Carrier A) →
  (a b : Nat → Carrier A) →
  PrimePowerHeckeSystem A scale a →
  PrimePowerHeckeSystem A scale b →
  a (suc zero) ≡ b (suc zero) →
  (n : Nat) → a n ≡ b n
primePowerDeterminedByPrimeEigenvalue A scale a b ha hb firstAgreement n =
  proj₁ (primePowerPairUniqueness A scale a b ha hb firstAgreement n)

------------------------------------------------------------------------
-- Exact two-prime/3-smooth assembly of the recurrence lanes.
------------------------------------------------------------------------

smooth23Coefficient :
  (A : RecurrenceCoefficientAlgebra) →
  (a2 a3 : Nat → Carrier A) →
  Nat → Nat → Carrier A
smooth23Coefficient A a2 a3 i j = mul A (a2 i) (a3 j)

smooth23DeterminedByTwoPrimeEigenvalues :
  (A : RecurrenceCoefficientAlgebra) →
  (scale2 scale3 : Carrier A) →
  (a2 b2 a3 b3 : Nat → Carrier A) →
  PrimePowerHeckeSystem A scale2 a2 →
  PrimePowerHeckeSystem A scale2 b2 →
  PrimePowerHeckeSystem A scale3 a3 →
  PrimePowerHeckeSystem A scale3 b3 →
  a2 (suc zero) ≡ b2 (suc zero) →
  a3 (suc zero) ≡ b3 (suc zero) →
  (i j : Nat) →
  smooth23Coefficient A a2 a3 i j ≡ smooth23Coefficient A b2 b3 i j
smooth23DeterminedByTwoPrimeEigenvalues
  A scale2 scale3 a2 b2 a3 b3 ha2 hb2 ha3 hb3 agree2 agree3 i j =
  cong₂ (mul A)
    (primePowerDeterminedByPrimeEigenvalue A scale2 a2 b2 ha2 hb2 agree2 i)
    (primePowerDeterminedByPrimeEigenvalue A scale3 a3 b3 ha3 hb3 agree3 j)

------------------------------------------------------------------------
-- The low square coefficient follows immediately from the recurrence.
------------------------------------------------------------------------

primeSquareFormula :
  (A : RecurrenceCoefficientAlgebra) →
  (scale : Carrier A) →
  (a : Nat → Carrier A) →
  (ha : PrimePowerHeckeSystem A scale a) →
  a 2
  ≡ sub A
      (mul A (a 1) (a 1))
      (mul A scale (a 0))
primeSquareFormula A scale a ha = primePowerRecurrence ha zero

record AristotleHeckeRecurrenceBoundary : Set where
  field
    primePowerUniquenessConstructed : Bool
    primePowerUniquenessConstructedIsTrue : primePowerUniquenessConstructed ≡ true
    smooth23UniquenessConstructed : Bool
    smooth23UniquenessConstructedIsTrue : smooth23UniquenessConstructed ≡ true
    arbitraryNatFactorisationClosureConstructedHere : Bool
    arbitraryNatFactorisationClosureConstructedHereIsFalse :
      arbitraryNatFactorisationClosureConstructedHere ≡ false

canonicalAristotleHeckeRecurrenceBoundary : AristotleHeckeRecurrenceBoundary
canonicalAristotleHeckeRecurrenceBoundary = record
  { primePowerUniquenessConstructed = true
  ; primePowerUniquenessConstructedIsTrue = refl
  ; smooth23UniquenessConstructed = true
  ; smooth23UniquenessConstructedIsTrue = refl
  ; arbitraryNatFactorisationClosureConstructedHere = false
  ; arbitraryNatFactorisationClosureConstructedHereIsFalse = refl
  }
