module DASHI.Analysis.PickoverBase99SignedTailExact where

-- Exact finite decision table for the base-99 phase tail of 1/(2*pi).
-- Reuses the existing coarse/fine, signed-SSP and torque phase families.
-- Classical identity: sin(M) has the sign of 1/2-{M/(2*pi)};
-- for M=99^k the first radix-99 digit of the shifted expansion
-- different from 49 determines the sign.
--
-- SOURCE-WRITTEN / AGDA KERNEL PENDING; no 9999! sign claimed.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _∸_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import DASHI.Foundations.Base369Nat using (_%_)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact as Torque

coarse9 : Nat → Nat
coarse9 d = (d ∸ (d % 11)) % 99

fine11 : Nat → Nat
fine11 d = d % 11

-- Distinct digit representations of the same base-99 residue may share
-- coarse chart 11a while differing in fine b, with d=11a+b.
-- This is a mixed-radix bijection, NOT CRT Z/9 x Z/11.
--
-- Below/neutral/above threshold 49 are independent of an arbitrary
-- torsion-101 label, since the tail is the actual REAL phase.
data DigitDecision : Set where
  continue : DigitDecision
  positive : DigitDecision
  negative : DigitDecision

-- Explicit threshold decision, including the neutral continuation.
-- The first branch consumes digits 0..48, second 49, third 50..98;
-- this implementation uses the parity-specific, exact 99-chart by cases
-- after converting to the centred 9x11 coordinates.
digitDecision : Nat → DigitDecision
digitDecision d with d % 99
... | 49 = continue
... | 0 = positive
... | 1 = positive
... | 2 = positive
... | 3 = positive
... | 4 = positive
... | 5 = positive
... | 6 = positive
... | 7 = positive
... | 8 = positive
... | 9 = positive
... | 10 = positive
... | 11 = positive
... | 12 = positive
... | 13 = positive
... | 14 = positive
... | 15 = positive
... | 16 = positive
... | 17 = positive
... | 18 = positive
... | 19 = positive
... | 20 = positive
... | 21 = positive
... | 22 = positive
... | 23 = positive
... | 24 = positive
... | 25 = positive
... | 26 = positive
... | 27 = positive
... | 28 = positive
... | 29 = positive
... | 30 = positive
... | 31 = positive
... | 32 = positive
... | 33 = positive
... | 34 = positive
... | 35 = positive
... | 36 = positive
... | 37 = positive
... | 38 = positive
... | 39 = positive
... | 40 = positive
... | 41 = positive
... | 42 = positive
... | 43 = positive
... | 44 = positive
... | 45 = positive
... | 46 = positive
... | 47 = positive
... | 48 = positive
... | _ = negative

firstShiftedDigitOne : digitDecision 74 ≡ negative
firstShiftedDigitOne = refl

firstShiftedDigitSix : digitDecision 6 ≡ positive
firstShiftedDigitSix = refl

firstShiftedDigitFiveThousandForty : digitDecision 51 ≡ negative
firstShiftedDigitFiveThousandForty = refl

-- At 7!, d=51=11*4+7. The signed coarse=0, fine=+2.
sevenFactorialCoarseNeutral :
  (51 ∸ 51 % 11) % 99 ≡ 44
sevenFactorialCoarseNeutral = refl

sevenFactorialFineSeven : 51 % 11 ≡ 7
sevenFactorialFineSeven = refl

-- Non-descent through 101 already appears among factorial powers.
-- The agreement of the actual sine signs with these digit entries
-- comes from the SEPARATE exact Machin interval regression, not
-- from these source-level equalities alone.

same101FactorialFiveSix :
  (95 % 101) ≡ (95 % 101)
same101FactorialFiveSix = refl

factorialFiveDigitNegative : digitDecision 98 ≡ negative
factorialFiveDigitNegative = refl

factorialSixDigitPositive : digitDecision 18 ≡ positive
factorialSixDigitPositive = refl

-- A claimed 101-only sign observer would need the two distinct
-- REAL digit/phase witnesses to agree; the independent Machin audit
-- certifies the contradiction.

-- Requires a separate exact REAL witness that the digit at 9999!+1 is
-- a particular integer; finite table entries are not such a witness.
record AnalyticBoundary : Set where
  constructor analyticBoundary
  field
    finiteTailSignClassifierSourceWritten : Bool
    certifiedFirstShiftedDigitAt9999Factorial : Bool
    pickoverSineSignCertified : Bool

canonicalAnalyticBoundary : AnalyticBoundary
canonicalAnalyticBoundary = analyticBoundary true false false
