module DASHI.ComputerScience.TekumWheelStateParityExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_; [m+kn]%n≡m%n)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Hunhold Proposition 1: the ordinary wheel splits into four equal sectors
-- exactly at even widths.  The arithmetic core is the period-two residue
-- law
--
--   3^n mod 4 = 1  iff n is even,
--   3^n mod 4 = 3  iff n is odd.
--
-- Since 5 mod 4 = 1, this is the non-truncated modular normal form of
-- 4 | (3^n - 5).  Keeping the theorem in residue form avoids Nat monus at
-- tiny widths where the five distinguished states already exceed 3^n.
------------------------------------------------------------------------

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

availableAfterFiveSpecials : Nat → Nat
availableAfterFiveSpecials n = pow3 n ∸ 5

quadrantRemainder : Nat → Nat
quadrantRemainder n = availableAfterFiveSpecials n % 4

instance
  nonZero4 : NonZero 4
  nonZero4 = nonZero

-- Two exponent steps multiply by nine, and 9x = x + (2x)4.
pow3TwoStep :
  (n : Nat) →
  pow3 (suc (suc n)) ≡ pow3 n + (2 * pow3 n) * 4
pow3TwoStep n =
  solve 1
    (λ x →
      con 3 :* (con 3 :* x)
      := x :+ ((con 2 :* x) :* con 4))
    refl
    (pow3 n)

pow3Mod4TwoStep :
  (n : Nat) →
  pow3 (suc (suc n)) % 4 ≡ pow3 n % 4
pow3Mod4TwoStep n =
  trans
    (cong (λ x → x % 4) (pow3TwoStep n))
    ([m+kn]%n≡m%n (pow3 n) (2 * pow3 n) 4)

------------------------------------------------------------------------
-- Indexed parity witnesses avoid importing a second semantic parity coding.
------------------------------------------------------------------------

data EvenWidth : Nat → Set where
  evenZero : EvenWidth zero
  evenPlusTwo : ∀ {n} → EvenWidth n → EvenWidth (suc (suc n))

data OddWidth : Nat → Set where
  oddOne : OddWidth (suc zero)
  oddPlusTwo : ∀ {n} → OddWidth n → OddWidth (suc (suc n))

classifyWidth :
  (n : Nat) → EvenWidth n ⊎ OddWidth n
classifyWidth zero = inj₁ evenZero
classifyWidth (suc zero) = inj₂ oddOne
classifyWidth (suc (suc n)) with classifyWidth n
... | inj₁ even = inj₁ (evenPlusTwo even)
... | inj₂ odd = inj₂ (oddPlusTwo odd)

pow3Mod4Even :
  ∀ {n} → EvenWidth n → pow3 n % 4 ≡ 1
pow3Mod4Even evenZero = refl
pow3Mod4Even {n = suc (suc n)} (evenPlusTwo even) =
  trans (pow3Mod4TwoStep n) (pow3Mod4Even even)

pow3Mod4Odd :
  ∀ {n} → OddWidth n → pow3 n % 4 ≡ 3
pow3Mod4Odd oddOne = refl
pow3Mod4Odd {n = suc (suc n)} (oddPlusTwo odd) =
  trans (pow3Mod4TwoStep n) (pow3Mod4Odd odd)

pow3Mod4OneImpliesEvenWidth :
  ∀ {n} → pow3 n % 4 ≡ 1 → EvenWidth n
pow3Mod4OneImpliesEvenWidth {n} residue with classifyWidth n
... | inj₁ even = even
... | inj₂ odd with trans (sym (pow3Mod4Odd odd)) residue
...   | ()

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A
open Iff public

wheelQuarterIntegralityIffEvenWidth :
  (n : Nat) → Iff (pow3 n % 4 ≡ 1) (EvenWidth n)
wheelQuarterIntegralityIffEvenWidth n =
  iff pow3Mod4OneImpliesEvenWidth pow3Mod4Even

------------------------------------------------------------------------
-- Calibration rows retained as executable sanity checks on the source widths.
------------------------------------------------------------------------

width2QuadrantRemainderZero : quadrantRemainder 2 ≡ 0
width2QuadrantRemainderZero = refl

width4QuadrantRemainderZero : quadrantRemainder 4 ≡ 0
width4QuadrantRemainderZero = refl

width6QuadrantRemainderZero : quadrantRemainder 6 ≡ 0
width6QuadrantRemainderZero = refl

width1QuadrantRemainderNonzero : quadrantRemainder 1 ≡ 2
width1QuadrantRemainderNonzero = refl

width3QuadrantRemainderNonzero : quadrantRemainder 3 ≡ 2
width3QuadrantRemainderNonzero = refl

record TekumWheelParityBoundary : Set where
  constructor tekumWheelParityBoundary
  field
    fiveDistinguishedWheelStatesRetained : Bool
    evenWidthFourQuadrantPattern : Bool
    oddWidthFailsSameFourWaySplit : Bool
    generalModuloFourParityTheoremPaid : Bool

canonicalTekumWheelParityBoundary : TekumWheelParityBoundary
canonicalTekumWheelParityBoundary =
  tekumWheelParityBoundary true true true true
