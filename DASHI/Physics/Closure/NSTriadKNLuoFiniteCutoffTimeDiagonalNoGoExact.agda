module DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffTimeDiagonalNoGoExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Mathematical ingredient: the classical distinction between pointwise and
-- uniform convergence.
-- Title: "Finite cutoff-time diagonal no-go".
-- Author: DASHI repository contributors.
-- DOI: not applicable; this is a repository-original exact counterexample.
--
-- PURPOSE
-- Exhibit the precise limit failure that a Clay-path proof must exclude.
-- Define an error which is one only on the cutoff/time diagonal.  For every
-- fixed terminal index t, every strictly larger cutoff kills the error
-- exactly; nevertheless the diagonal error remains one at every scale.
--
-- Hence pointwise cutoff convergence at each fixed time does not imply the
-- uniform control needed as q -> infinity and t approaches a candidate
-- maximal time.  A quantitative joint modulus is a genuine theorem, not a
-- bookkeeping detail.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)

cutoffTimeSpike : Nat → Nat → ℚ
cutoffTimeSpike zero zero = 1ℚ
cutoffTimeSpike zero (suc time) = 0ℚ
cutoffTimeSpike (suc cutoff) zero = 0ℚ
cutoffTimeSpike (suc cutoff) (suc time) =
  cutoffTimeSpike cutoff time

diagonalNeverVanishes :
  (index : Nat) →
  cutoffTimeSpike index index ≡ 1ℚ
diagonalNeverVanishes zero = refl
diagonalNeverVanishes (suc index) =
  diagonalNeverVanishes index

data StrictlyAbove : Nat → Nat → Set where
  aboveZero :
    (extra : Nat) →
    StrictlyAbove (suc extra) zero

  bothSuccessors :
    ∀ {cutoff time} →
    StrictlyAbove cutoff time →
    StrictlyAbove (suc cutoff) (suc time)

strictlyLargerCutoffVanishes :
  ∀ {cutoff time} →
  StrictlyAbove cutoff time →
  cutoffTimeSpike cutoff time ≡ 0ℚ
strictlyLargerCutoffVanishes (aboveZero extra) = refl
strictlyLargerCutoffVanishes (bothSuccessors above) =
  strictlyLargerCutoffVanishes above

oneCutoffPastFixedTime :
  (time : Nat) →
  StrictlyAbove (suc time) time
oneCutoffPastFixedTime zero = aboveZero zero
oneCutoffPastFixedTime (suc time) =
  bothSuccessors (oneCutoffPastFixedTime time)

oneCutoffPastFixedTimeVanishes :
  (time : Nat) →
  cutoffTimeSpike (suc time) time ≡ 0ℚ
oneCutoffPastFixedTimeVanishes time =
  strictlyLargerCutoffVanishes (oneCutoffPastFixedTime time)
