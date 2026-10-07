module DASHI.Analysis.CollatzSyracuseRationalDriftApproximantsExact where

------------------------------------------------------------------------
-- EXACT INTEGER APPROXIMANTS TO THE SYRACUSE DRIFT THRESHOLD
--
-- The parametric tail theorem only needs 3^a <= 2^b.  These source-written
-- instances improve the coarse 5/8 threshold without introducing logarithms.
--
--   3^5  = 243       <= 256       = 2^8
--   3^17 = 129140163 <= 134217728 = 2^27
--
-- 17/27 is closer to log_3(2) than 5/8, so it admits more parity words as
-- deterministic descent words while retaining an exact integer Chernoff tail.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Unit.Base using (tt)

import DASHI.Core.BinaryWordIntegerChernoffExact as Chernoff
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParityDescentEventExact as Event
import DASHI.Analysis.CollatzSyracuseRationalDriftTailExact as Rational

fiveEightPower :
  Affine.powNat 3 5 ≤ Affine.powNat 2 8
fiveEightPower = NatP.≤ᵇ⇒≤ 243 256 tt

seventeenTwentySevenPower :
  Affine.powNat 3 17 ≤ Affine.powNat 2 27
seventeenTwentySevenPower = NatP.≤ᵇ⇒≤ 129140163 134217728 tt

fiveEightTail :
  (n : Nat) →
  Chernoff.powNat 2 (5 * n + 1)
    * Event.badWordCount (8 * n + 1)
  ≤ Chernoff.powNat 3 (8 * n + 1)
fiveEightTail n =
  Rational.rationalBadWordBound 5 8 n fiveEightPower

seventeenTwentySevenTail :
  (n : Nat) →
  Chernoff.powNat 2 (17 * n + 1)
    * Event.badWordCount (27 * n + 1)
  ≤ Chernoff.powNat 3 (27 * n + 1)
seventeenTwentySevenTail n =
  Rational.rationalBadWordBound 17 27 n seventeenTwentySevenPower

record RationalApproximantBoundary : Set where
  constructor rationalApproximantBoundary
  field
    fiveEightRecovered : Nat
    seventeenTwentySevenOwned : Nat
    logarithmUsedInProof : Nat
    thresholdCanBeImprovedByIntegerPowers : Nat
    universalStoppingOwned : Nat

canonicalRationalApproximantBoundary : RationalApproximantBoundary
canonicalRationalApproximantBoundary =
  rationalApproximantBoundary 1 1 0 1 0
