module DASHI.Arithmetic.PrimeModSixSieveExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- G. H. Hardy and E. M. Wright, revised by D. R. Heath-Brown and J. H.
-- Silverman,
-- "An Introduction to the Theory of Numbers", sixth edition,
-- Oxford University Press, 2008.
-- DOI: 10.1093/oso/9780199219858.001.0001.
--
-- DASHI CONTRIBUTION
--
-- Replace the tracked-prime mod-6 lookup pattern by a generic theorem.
-- Every prime p > 3 is congruent to 1 or 5 modulo 6.  The proof is fully
-- constructive: the four excluded residue classes explicitly manufacture a
-- divisor 2 or 3, contradicting irreducibility of p.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (_/_; _%_)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n<n)
open import Data.Nat.Divisibility using (_∣_; _∤_; divides)
open import Data.Nat.Primality using (Prime; prime⇒irreducible)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

------------------------------------------------------------------------
-- The four composite residue classes modulo six.
------------------------------------------------------------------------

remainder0Even :
  (q : Nat) →
  0 + q * 6 ≡ (3 * q) * 2
remainder0Even =
  solve 1
    (λ q →
      con 0 :+ q :* con 6
      :=
      (con 3 :* q) :* con 2)
    refl

remainder2Even :
  (q : Nat) →
  2 + q * 6 ≡ (1 + 3 * q) * 2
remainder2Even =
  solve 1
    (λ q →
      con 2 :+ q :* con 6
      :=
      (con 1 :+ con 3 :* q) :* con 2)
    refl

remainder4Even :
  (q : Nat) →
  4 + q * 6 ≡ (2 + 3 * q) * 2
remainder4Even =
  solve 1
    (λ q →
      con 4 :+ q :* con 6
      :=
      (con 2 :+ con 3 :* q) :* con 2)
    refl

remainder3DivisibleByThree :
  (q : Nat) →
  3 + q * 6 ≡ (1 + 2 * q) * 3
remainder3DivisibleByThree =
  solve 1
    (λ q →
      con 3 :+ q :* con 6
      :=
      (con 1 :+ con 2 :* q) :* con 3)
    refl

twoDividesFromRemainder0 :
  ∀ {p} →
  p % 6 ≡ 0 →
  2 ∣ p
twoDividesFromRemainder0 {p} remainder =
  divides
    (3 * (p / 6))
    (trans
      (m≡m%n+[m/n]*n p 6)
      (trans
        (cong (λ r → r + (p / 6) * 6) remainder)
        (remainder0Even (p / 6))))

twoDividesFromRemainder2 :
  ∀ {p} →
  p % 6 ≡ 2 →
  2 ∣ p
twoDividesFromRemainder2 {p} remainder =
  divides
    (1 + 3 * (p / 6))
    (trans
      (m≡m%n+[m/n]*n p 6)
      (trans
        (cong (λ r → r + (p / 6) * 6) remainder)
        (remainder2Even (p / 6))))

twoDividesFromRemainder4 :
  ∀ {p} →
  p % 6 ≡ 4 →
  2 ∣ p
twoDividesFromRemainder4 {p} remainder =
  divides
    (2 + 3 * (p / 6))
    (trans
      (m≡m%n+[m/n]*n p 6)
      (trans
        (cong (λ r → r + (p / 6) * 6) remainder)
        (remainder4Even (p / 6))))

threeDividesFromRemainder3 :
  ∀ {p} →
  p % 6 ≡ 3 →
  3 ∣ p
threeDividesFromRemainder3 {p} remainder =
  divides
    (1 + 2 * (p / 6))
    (trans
      (m≡m%n+[m/n]*n p 6)
      (trans
        (cong (λ r → r + (p / 6) * 6) remainder)
        (remainder3DivisibleByThree (p / 6))))

------------------------------------------------------------------------
-- A prime represented as 4+n is automatically greater than three.
------------------------------------------------------------------------

primeAboveThreeNotDivisibleByTwo :
  (n : Nat) →
  Prime (4 + n) →
  2 ∤ (4 + n)
primeAboveThreeNotDivisibleByTwo n primeProof divisor
  with prime⇒irreducible primeProof divisor
... | inj₁ ()
... | inj₂ ()

primeAboveThreeNotDivisibleByThree :
  (n : Nat) →
  Prime (4 + n) →
  3 ∤ (4 + n)
primeAboveThreeNotDivisibleByThree n primeProof divisor
  with prime⇒irreducible primeProof divisor
... | inj₁ ()
... | inj₂ ()

------------------------------------------------------------------------
-- Generic prime-wheel theorem.
------------------------------------------------------------------------

PrimeModSixClass : Nat → Set
PrimeModSixClass p =
  p % 6 ≡ 1 ⊎ p % 6 ≡ 5

primeAboveThreeModSix :
  (n : Nat) →
  Prime (4 + n) →
  PrimeModSixClass (4 + n)
primeAboveThreeModSix n primeProof
  with (4 + n) % 6 | m%n<n (4 + n) 6
... | 0 | _ =
  ⊥-elim
    (primeAboveThreeNotDivisibleByTwo n primeProof
      (twoDividesFromRemainder0 refl))
... | 1 | _ = inj₁ refl
... | 2 | _ =
  ⊥-elim
    (primeAboveThreeNotDivisibleByTwo n primeProof
      (twoDividesFromRemainder2 refl))
... | 3 | _ =
  ⊥-elim
    (primeAboveThreeNotDivisibleByThree n primeProof
      (threeDividesFromRemainder3 refl))
... | 4 | _ =
  ⊥-elim
    (primeAboveThreeNotDivisibleByTwo n primeProof
      (twoDividesFromRemainder4 refl))
... | 5 | _ = inj₂ refl
... | suc (suc (suc (suc (suc (suc r))))) | ()
