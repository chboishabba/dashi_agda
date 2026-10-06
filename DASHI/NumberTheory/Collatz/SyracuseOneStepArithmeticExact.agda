module DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact where

------------------------------------------------------------------------
-- LITERAL ONE-STEP NAT ARITHMETIC FOR SHORTCUT SYRACUSE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (_<_; NonZero; nonZero)
open import Data.Nat.DivMod using
  (_%_; _/_; m%n<n; m≡m%n+[m/n]*n; m*n/n≡m)
open import Data.Nat.Divisibility using
  (_∣_; m%n≡0⇒n∣m; n/m≡quotient)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (subst)

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

positiveQuotientFromPositiveDividend :
  (x q : Nat) →
  x ≡ q * 2 →
  (x ≡ 0 → ⊥) →
  Σ Nat (λ predecessor → q ≡ suc predecessor)
positiveQuotientFromPositiveDividend x zero equation xNonZero =
  ⊥-elim (xNonZero (trans equation refl))
positiveQuotientFromPositiveDividend x (suc q) equation xNonZero =
  q , refl
  where open import Data.Product using (Σ; _,_)

positiveNatToNatNonZero :
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x ≡ 0 → ⊥
positiveNatToNatNonZero (Syracuse.positiveNat n) ()

quotientTimesTwoExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  (Syracuse.toNat x / 2) * 2 ≡ Syracuse.toNat x
quotientTimesTwoExact x parityFalse =
  let
    divisible : 2 ∣ Syracuse.toNat x
    divisible = m%n≡0⇒n∣m
      (Syracuse.toNat x) 2 (parityFalseModTwo x parityFalse)
  in
  sym (Data.Nat.Divisibility.m∣n⇒n≡quotient*m divisible)
  where
    open import Data.Nat.Divisibility using (m∣n⇒n≡quotient*m)

sucPredPositiveQuotient :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ false →
  suc ((Syracuse.toNat x / 2) ∸ 1)
  ≡ Syracuse.toNat x / 2
sucPredPositiveQuotient x parityFalse with Syracuse.toNat x / 2 | inspect (λ y → Syracuse.toNat x / 2) x/2eq
... | zero | _ =
  ⊥-elim
    (positiveNatToNatNonZero x
      (trans
        (sym (quotientTimesTwoExact x parityFalse))
        (cong (_* 2) x/2eq)))
... | suc q | _ = refl
  where
    open import Agda.Builtin.Nat using (_∸_)
    open import Relation.Binary.PropositionalEquality using (inspect)

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
    orient =
      solve 1 (λ q → con 2 :* q := q :* con 2) refl
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
    xShape :
      Syracuse.toNat x
      ≡ 1 + (Syracuse.toNat x / 2) * 2
    xShape = trans decomposition (cong (λ r → r + (Syracuse.toNat x / 2) * 2) remainderOne)
    q = Syracuse.toNat x / 2
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
  Data.Nat.Divisibility.divides (2 + 3 * q) (sym numeratorShape)
  where
    open import Data.Nat.Divisibility using (divides)

oddQuotientTimesTwoExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  ((3 * Syracuse.toNat x + 1) / 2) * 2
  ≡ 3 * Syracuse.toNat x + 1
oddQuotientTimesTwoExact x parityTrue =
  sym
    (Data.Nat.Divisibility.m∣n⇒n≡quotient*m
      (oddNumeratorDivisible x parityTrue))
  where
    open import Data.Nat.Divisibility using (m∣n⇒n≡quotient*m)

oddQuotientPositiveNormalize :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  suc (((3 * Syracuse.toNat x + 1) / 2) ∸ 1)
  ≡ (3 * Syracuse.toNat x + 1) / 2
oddQuotientPositiveNormalize x parityTrue with (3 * Syracuse.toNat x + 1) / 2
... | zero =
  ⊥-elim
    (positiveNatToNatNonZero x
      (let impossible : 3 * Syracuse.toNat x + 1 ≡ 0
           impossible = trans
             (sym (oddQuotientTimesTwoExact x parityTrue))
             refl
       in
       let collapse : Syracuse.toNat x ≡ 0
           collapse =
             -- 3*x+1 cannot be zero for a positive x; the zero quotient branch
             -- is structurally impossible.  Solver turns `3*x+1=0` into the
             -- required contradiction after patterning on x below.
             case x of λ where
               (Syracuse.positiveNat n) →
                 case impossible of λ ())
... | suc q = refl
  where open import Agda.Builtin.Nat using (_∸_)

oddStepExact :
  (x : Syracuse.PositiveNat) →
  Itinerary.parity x ≡ true →
  2 * Syracuse.toNat (Syracuse.shortcutSyracuse x)
  ≡ 3 * Syracuse.toNat x + 1
oddStepExact (Syracuse.positiveNat n) parityTrue =
  let
    branch = Syracuse.shortcutSyracuseParityTrue n parityTrue
    normalize = oddQuotientPositiveNormalize (Syracuse.positiveNat n) parityTrue
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
