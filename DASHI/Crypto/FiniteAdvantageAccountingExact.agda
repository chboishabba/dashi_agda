module DASHI.Crypto.FiniteAdvantageAccountingExact where

------------------------------------------------------------------------
-- FINITE DISTINGUISHING ADVANTAGE ACCOUNTING
--
-- Exact finite-count layer between perfect recovery and probabilistic security
-- games.  No probability library is required: success is a numerator over a
-- declared finite trial count, and advantage is recorded relative to a supplied
-- baseline count.  This is bookkeeping infrastructure, not an IND-CCA proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

record FiniteSuccessExperiment : Set where
  constructor finiteSuccessExperiment
  field
    trials successes baselineSuccesses : Nat
    successesWithinTrials : successes ≤ trials
    baselineWithinTrials : baselineSuccesses ≤ trials

open FiniteSuccessExperiment public

record PositiveAdvantage
    (experiment : FiniteSuccessExperiment) : Set where
  constructor positiveAdvantage
  field
    gain : Nat
    successDecomposition :
      successes experiment ≡ baselineSuccesses experiment + gain

open PositiveAdvantage public

record PerfectSuccess
    (experiment : FiniteSuccessExperiment) : Set where
  constructor perfectSuccess
  field successesEqualTrials : successes experiment ≡ trials experiment

open PerfectSuccess public

------------------------------------------------------------------------
-- Canonical balanced binary two-trial experiment:
-- random-guess baseline 1/2, perfect success 2/2, exact gain numerator 1.
------------------------------------------------------------------------

twoTrials : FiniteSuccessExperiment
twoTrials =
  finiteSuccessExperiment 2 2 1
    (s≤s (s≤s z≤n))
    (s≤s z≤n)

perfectTwoTrials : PerfectSuccess twoTrials
perfectTwoTrials = perfectSuccess refl

perfectTwoTrialsGain : PositiveAdvantage twoTrials
perfectTwoTrialsGain = positiveAdvantage 1 refl

------------------------------------------------------------------------
-- Boundary: positive finite advantage is weaker than exact recovery, and an
-- experiment record by itself proves no computational feasibility statement.
------------------------------------------------------------------------
