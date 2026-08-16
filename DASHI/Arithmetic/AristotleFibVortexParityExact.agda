module DASHI.Arithmetic.AristotleFibVortexParityExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source module:
--   RequestProject.FibVortex
--   SHA-256 a93ad8757124c7aeb863c6813f3fc953be0665ad9d8b244f2367225983622560
--
-- The upstream project README requests @Aristotle-Harmonic attribution and
-- the commit trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY SOURCE / CONTEXT
-- D. D. Wall,
-- "Fibonacci Series Modulo m", The American Mathematical Monthly 67(6)
-- (1960), 525-532.
-- DOI: 10.1080/00029890.1960.11989541.
--
-- DASHI CONTRIBUTION
-- Complete the remaining finite cycle-sum surface of the upstream FibVortex
-- module on the existing NonaryTruth Fibonacci recurrence.  The positive
-- digital-root representative maps residue 0 to 9 and residues 1..8 to
-- themselves; the first twenty-four positive-index Fibonacci digital roots
-- sum exactly to 117 = 9 * 13.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Arithmetic.FibonacciNonaryPeriodExact as Fib
import Base369 as Base

positiveDigitalRootValue : Base.NonaryTruth → Nat
positiveDigitalRootValue Base.non-0 = 9
positiveDigitalRootValue Base.non-1 = 1
positiveDigitalRootValue Base.non-2 = 2
positiveDigitalRootValue Base.non-3 = 3
positiveDigitalRootValue Base.non-4 = 4
positiveDigitalRootValue Base.non-5 = 5
positiveDigitalRootValue Base.non-6 = 6
positiveDigitalRootValue Base.non-7 = 7
positiveDigitalRootValue Base.non-8 = 8

fibPositiveDigitalRoot : Nat → Nat
fibPositiveDigitalRoot n = positiveDigitalRootValue (Fib.fibResidue n)

firstTwentyFourPositiveFibDigitalRootSum : Nat
firstTwentyFourPositiveFibDigitalRootSum =
    fibPositiveDigitalRoot 1
  + fibPositiveDigitalRoot 2
  + fibPositiveDigitalRoot 3
  + fibPositiveDigitalRoot 4
  + fibPositiveDigitalRoot 5
  + fibPositiveDigitalRoot 6
  + fibPositiveDigitalRoot 7
  + fibPositiveDigitalRoot 8
  + fibPositiveDigitalRoot 9
  + fibPositiveDigitalRoot 10
  + fibPositiveDigitalRoot 11
  + fibPositiveDigitalRoot 12
  + fibPositiveDigitalRoot 13
  + fibPositiveDigitalRoot 14
  + fibPositiveDigitalRoot 15
  + fibPositiveDigitalRoot 16
  + fibPositiveDigitalRoot 17
  + fibPositiveDigitalRoot 18
  + fibPositiveDigitalRoot 19
  + fibPositiveDigitalRoot 20
  + fibPositiveDigitalRoot 21
  + fibPositiveDigitalRoot 22
  + fibPositiveDigitalRoot 23
  + fibPositiveDigitalRoot 24

fibDigitalRootCycleSumIs117 :
  firstTwentyFourPositiveFibDigitalRootSum ≡ 117
fibDigitalRootCycleSumIs117 = refl

fibDigitalRootCycleSumIsNineTimesThirteen :
  firstTwentyFourPositiveFibDigitalRootSum ≡ 9 * 13
fibDigitalRootCycleSumIsNineTimesThirteen = refl
