module DASHI.Arithmetic.SignedSSPPrimeOffsetMacroExact where

------------------------------------------------------------------------
-- SOURCE / ATTRIBUTION
--
-- John H. Conway: FRACTRAN ordered fractional integer execution,
-- original construction 1972-1987 (Conway's PRIMEGAME is distinct
-- from this offset macro).
-- FRACDASH owners: signed exponent-vector IR, paired-prime register
-- realization, exact-step compiled execution (see BRIDGE_CORRECTNESS.md).
-- DASHI.Biology.SignedSSPFRACTRANWeaveExact owns the SSP signed direction.
--
-- NEW theorem owner: exact two-step FRACTRAN multiplication/divisibility
-- certificates for +2 and -2 *exponents*, for every Nat p (minus p>=2).
--
-- IMPORTANT: A power-of-two exponent value is not automatically prime.
-- These are separately run singleton fraction macros; a sequence that
-- hands each PRIMEGAME output to this macro needs a compiler/readout gate.
-- No unbounded prime-pair or signed analytic advantage is claimed.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties using (+-comm)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

two : Nat
two = 2

-- The power-of-two readout is the same arithmetic coding used by
-- Conway's PRIMEGAME. The compiled SSP register carriers are separate.
powerTwo : Nat → Nat
powerTwo zero = 1
powerTwo (suc k) = 2 * powerTwo k

plusSource : Nat → Nat
plusSource p = 9 * powerTwo p

plusMiddle : Nat → Nat
plusMiddle p = 6 * powerTwo p

plusOutput : Nat → Nat
plusOutput p = 4 * powerTwo p

minusSource : Nat → Nat
minusSource k = 36 * powerTwo k

minusMiddle : Nat → Nat
minusMiddle k = 6 * powerTwo k

minusOutput : Nat → Nat
minusOutput k = powerTwo k

-- A FRACTRAN step numerator/denominator satisfies:
--   source*Numerator = target*Denominator,
-- and the denominator divides source.
--
-- This is stronger than a bare arithmetic identity because it carries
-- a constructive applicability certificate. It does not assert global
-- ordered-program first-applicable selection; the macro has one rule.
record ExactFractionStep
    (numerator denominator source target : Nat) : Set where
  constructor fractionStep
  field
    guard : denominator ∣ source
    arithmetic : source * numerator ≡ target * denominator

open ExactFractionStep public

record ExactTwoStepMacro
    (numerator denominator start middle output : Nat) : Set where
  constructor twoStepMacro
  field
    first : ExactFractionStep numerator denominator start middle
    second : ExactFractionStep numerator denominator middle output

open ExactTwoStepMacro public

-- Generic literal laws specialised to the arbitrary power-of-two
-- factor. Data.Nat.Solver is the pre-existing repository proof style.
plusGuardFirst : (v : Nat) → 9 * v ≡ (3 * v) * 3
plusGuardFirst = solve 1
  (λ v → con 9 :* v := (con 3 :* v) :* con 3) refl

plusGuardSecond : (v : Nat) → 6 * v ≡ (2 * v) * 3
plusGuardSecond = solve 1
  (λ v → con 6 :* v := (con 2 :* v) :* con 3) refl

plusArithmeticFirst : (v : Nat) →
  (9 * v) * 2 ≡ (6 * v) * 3
plusArithmeticFirst = solve 1
  (λ v → (con 9 :* v) :* con 2 :=
         (con 6 :* v) :* con 3) refl

plusArithmeticSecond : (v : Nat) →
  (6 * v) * 2 ≡ (4 * v) * 3
plusArithmeticSecond = solve 1
  (λ v → (con 6 :* v) :* con 2 :=
         (con 4 :* v) :* con 3) refl

-- This is a genuine two-step FRACTRAN [+2] program [2/3].
-- Both steps are enabled with explicit divisibility witnesses.
plusTwoFractionMacro : (p : Nat) →
  ExactTwoStepMacro 2 3 (plusSource p) (plusMiddle p) (plusOutput p)
plusTwoFractionMacro p = twoStepMacro
  (fractionStep
    (divides (3 * powerTwo p) (plusGuardFirst (powerTwo p)))
    (plusArithmeticFirst (powerTwo p)))
  (fractionStep
    (divides (2 * powerTwo p) (plusGuardSecond (powerTwo p)))
    (plusArithmeticSecond (powerTwo p)))

minusGuardFirst : (v : Nat) →
  36 * v ≡ (6 * v) * 6
minusGuardFirst = solve 1
  (λ v → con 36 :* v := (con 6 :* v) :* con 6) refl

minusGuardSecond : (v : Nat) →
  6 * v ≡ v * 6
minusGuardSecond = solve 1
  (λ v → con 6 :* v := v :* con 6) refl

minusArithmeticFirst : (v : Nat) →
  (36 * v) * 1 ≡ (6 * v) * 6
minusArithmeticFirst = solve 1
  (λ v → (con 36 :* v) :* con 1 :=
         (con 6 :* v) :* con 6) refl

minusArithmeticSecond : (v : Nat) →
  (6 * v) * 1 ≡ v * 6
minusArithmeticSecond = solve 1
  (λ v → (con 6 :* v) :* con 1 :=
         v :* con 6) refl

-- p = 2+k, k arbitrary. Two steps of [1/6] yield 2^k exactly.
-- There is no illegal attempt to subtract 2 from zero or one.
minusTwoFractionMacro : (k : Nat) →
  ExactTwoStepMacro 1 6 (minusSource k) (minusMiddle k) (minusOutput k)
minusTwoFractionMacro k = twoStepMacro
  (fractionStep
    (divides (6 * powerTwo k) (minusGuardFirst (powerTwo k)))
    (minusArithmeticFirst (powerTwo k)))
  (fractionStep
    (divides (powerTwo k) (minusGuardSecond (powerTwo k)))
    (minusArithmeticSecond (powerTwo k)))

minusStartIsPrimeEncoded : (k : Nat) →
  minusSource k ≡ 9 * powerTwo (suc (suc k))
minusStartIsPrimeEncoded k =
  (solve 1
    (λ v → con 36 :* v :=
           con 9 :* (con 2 :* (con 2 :* v))) refl)
    (powerTwo k)

plusOutputHasOffsetExponent : (p : Nat) →
  plusOutput p ≡ powerTwo (p + 2)
plusOutputHasOffsetExponent p =
  trans
    ((solve 1
       (λ v → con 4 :* v :=
              con 2 :* (con 2 :* v)) refl)
       (powerTwo p))
    (cong powerTwo (+-comm 2 p))

minusOutputHasOffsetExponent : (k : Nat) →
  minusOutput k ≡ powerTwo k
minusOutputHasOffsetExponent k = refl

-- Orientation uses the ORIGINAL signed SSP constructors; sign and
-- arithmetic output are distinct pieces of the machine certificate.
signedPlusTwo : Signed.SignedMultiplicity
signedPlusTwo = Signed.positiveMultiplicity two

signedMinusTwo : Signed.SignedMultiplicity
signedMinusTwo = Signed.negativeMultiplicity two

signedPlusIsForward :
  Signed.orientationOfMultiplicity signedPlusTwo
  ≡ Signed.forwardOrientation
signedPlusIsForward = refl

signedMinusIsInverse :
  Signed.orientationOfMultiplicity signedMinusTwo
  ≡ Signed.inverseOrientation
signedMinusIsInverse = refl

signedOppositesAreInvolutive :
  Signed.negateMultiplicity
    (Signed.negateMultiplicity signedPlusTwo)
  ≡ signedPlusTwo
signedOppositesAreInvolutive = refl

minusIsNegationOfPlus :
  Signed.negateMultiplicity signedPlusTwo ≡ signedMinusTwo
minusIsNegationOfPlus = refl

plusIsNegationOfMinus :
  Signed.negateMultiplicity signedMinusTwo ≡ signedPlusTwo
plusIsNegationOfMinus = refl
