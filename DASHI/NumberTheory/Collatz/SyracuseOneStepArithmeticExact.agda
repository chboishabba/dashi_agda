module DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact where

------------------------------------------------------------------------
-- LITERAL ONE-STEP NAT ARITHMETIC FOR SHORTCUT SYRACUSE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat using (_∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using
  (_%_; _/_; m%n<n; m≡m%n+[m/n]*n; m≥n⇒m/n>0)
open import Data.Nat.Divisibility using
  (_∣_; divides; quotient; m%n≡0⇒n∣m; m∣n⇒n≡quotient*m; n/m≡quotient)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateCompilerExact as AffineCompiler

instance
  nonZeroTwo : NonZero 2
  nonZeroTwo = nonZero

parityFalseModTwo :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  Syracuse.toNat x % 2 ≡ 0
parityFalseModTwo (Syracuse.positiveNat n) with suc n % 2
... | zero = λ _ → refl
... | suc _ = λ ()

remainderSucBelowTwoIsOne :
  (r : Nat) →
  suc r < 2 →
  suc r ≡ 1
remainderSucBelowTwoIsOne zero bound = refl
remainderSucBelowTwoIsOne (suc r) ()

parityTrueModTwo :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  Syracuse.toNat x % 2 ≡ 1
parityTrueModTwo (Syracuse.positiveNat n) with suc n % 2
... | zero = λ ()
... | suc r = λ _ → remainderSucBelowTwoIsOne r (m%n<n (suc n) 2)

sucPredOfPositive :
  (q : Nat) →
  0 < q →
  suc (q ∸ 1) ≡ q
sucPredOfPositive zero ()
sucPredOfPositive (suc q) positive = refl

evenQuotientPositive :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  0 < Syracuse.toNat x / 2
evenQuotientPositive (Syracuse.positiveNat zero) ()
evenQuotientPositive (Syracuse.positiveNat (suc n)) parityFalse =
  m≥n⇒m/n>0 (s≤s (s≤s z≤n))

numeratorAtLeastTwo :
  (n : Nat) →
  2 ≤ 3 * suc n + 1
numeratorAtLeastTwo n = s≤s (s≤s z≤n)

oddQuotientPositive :
  (x : Syracuse.PositiveNat) →
  0 < (3 * Syracuse.toNat x + 1) / 2
oddQuotientPositive (Syracuse.positiveNat n) =
  m≥n⇒m/n>0 (numeratorAtLeastTwo n)

quotientTimesTwoExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  (Syracuse.toNat x / 2) * 2 ≡ Syracuse.toNat x
quotientTimesTwoExact x parityFalse =
  let
    witness = m%n≡0⇒n∣m
      (Syracuse.toNat x) 2
      (parityFalseModTwo x parityFalse)
    quotientAgreement :
      Syracuse.toNat x / 2 ≡ quotient witness
    quotientAgreement = n/m≡quotient witness
    witnessExact :
      quotient witness * 2 ≡ Syracuse.toNat x
    witnessExact = sym (m∣n⇒n≡quotient*m witness)
  in
  trans (cong (_* 2) quotientAgreement) witnessExact

sucPredPositiveQuotient :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  suc ((Syracuse.toNat x / 2) ∸ 1)
  ≡ Syracuse.toNat x / 2
sucPredPositiveQuotient x parityFalse =
  sucPredOfPositive
    (Syracuse.toNat x / 2)
    (evenQuotientPositive x parityFalse)

evenStepExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  2 * Syracuse.toNat (Syracuse.shortcutSyracuse x)
  ≡ Syracuse.toNat x
evenStepExact (Syracuse.positiveNat n) parityFalse =
  let
    branch = Syracuse.shortcutSyracuseParityFalse n parityFalse
    qNormalize = sucPredPositiveQuotient (Syracuse.positiveNat n) parityFalse
    quotientExact = quotientTimesTwoExact (Syracuse.positiveNat n) parityFalse
    orient :
      2 * (Syracuse.toNat (Syracuse.positiveNat n) / 2)
      ≡ (Syracuse.toNat (Syracuse.positiveNat n) / 2) * 2
    orient = solve 1 (λ q → con 2 :* q := q :* con 2) refl
  in
  trans
    (cong (λ y → 2 * Syracuse.toNat y) branch)
    (trans
      (cong (2 *_) qNormalize)
      (trans orient quotientExact))

oddNumeratorDivisible :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  2 ∣ (3 * Syracuse.toNat x + 1)
oddNumeratorDivisible x parityTrue =
  let
    remainderOne = parityTrueModTwo x parityTrue
    decomposition = m≡m%n+[m/n]*n (Syracuse.toNat x) 2
    q = Syracuse.toNat x / 2
    xShape : Syracuse.toNat x ≡ 1 + q * 2
    xShape =
      trans decomposition
        (cong (λ r → r + q * 2) remainderOne)
    numeratorShape :
      3 * Syracuse.toNat x + 1 ≡ (2 + 3 * q) * 2
    numeratorShape =
      trans
        (cong (λ value → 3 * value + 1) xShape)
        (solve 1
          (λ q →
            (con 3 :* (con 1 :+ (q :* con 2))) :+ con 1
            :=
            (con 2 :+ (con 3 :* q)) :* con 2)
          refl)
  in
  divides (2 + 3 * q) numeratorShape

oddQuotientTimesTwoExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  ((3 * Syracuse.toNat x + 1) / 2) * 2
  ≡ 3 * Syracuse.toNat x + 1
oddQuotientTimesTwoExact x parityTrue =
  let
    witness = oddNumeratorDivisible x parityTrue
    quotientAgreement :
      (3 * Syracuse.toNat x + 1) / 2 ≡ quotient witness
    quotientAgreement = n/m≡quotient witness
    witnessExact :
      quotient witness * 2 ≡ 3 * Syracuse.toNat x + 1
    witnessExact = sym (m∣n⇒n≡quotient*m witness)
  in
  trans (cong (_* 2) quotientAgreement) witnessExact

oddQuotientPositiveNormalize :
  (x : Syracuse.PositiveNat) →
  suc (((3 * Syracuse.toNat x + 1) / 2) ∸ 1)
  ≡ (3 * Syracuse.toNat x + 1) / 2
oddQuotientPositiveNormalize x =
  sucPredOfPositive
    ((3 * Syracuse.toNat x + 1) / 2)
    (oddQuotientPositive x)

oddStepExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  2 * Syracuse.toNat (Syracuse.shortcutSyracuse x)
  ≡ 3 * Syracuse.toNat x + 1
oddStepExact (Syracuse.positiveNat n) parityTrue =
  let
    branch = Syracuse.shortcutSyracuseParityTrue n parityTrue
    normalize = oddQuotientPositiveNormalize (Syracuse.positiveNat n)
    quotientExact = oddQuotientTimesTwoExact (Syracuse.positiveNat n) parityTrue
    orient :
      2 * ((3 * suc n + 1) / 2)
      ≡ ((3 * suc n + 1) / 2) * 2
    orient = solve 1 (λ q → con 2 :* q := q :* con 2) refl
  in
  trans
    (cong (λ y → 2 * Syracuse.toNat y) branch)
    (trans (cong (2 *_) normalize) (trans orient quotientExact))

canonicalOneStepAffineSource : AffineCompiler.SyracuseOneStepAffineSource
canonicalOneStepAffineSource = record
  { AffineCompiler.evenStepExact = evenStepExact
  ; AffineCompiler.oddStepExact = oddStepExact
  }
