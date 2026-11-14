module DASHI.Moonshine.OggSSPClimbingGymPhaseControlExact where

------------------------------------------------------------------------
-- PHASE-SENSITIVE OGG / NON-OGG CONTROL RECEIPT
--
-- Executable producer:
--   scripts/monster_climbing_gym_phase_control.py
--
-- On the same first-849 numerical zeta-zero cache as the climbing-gym replay,
-- define
--
--   C(t) = sum_{p in Ogg15} p^(i t)
--          - 3 sum_{q in nonOgg5} q^(i t).
--
-- The coefficient sum is exactly 15 - 3*5 = 0.  The executable control then
-- enumerates every choice of five controls among the twenty combined primes,
-- C(20,5)=15504 assignments, with no RNG.
--
-- Two diagnostics are retained deliberately without post-hoc promotion:
--   * mean |C|^2: actual partition has 3459 / 15504 assignments at or below;
--   * |mean C|:   actual partition has 541 / 15504 assignments at or above.
--
-- Hence the energy statistic is plainly non-extreme.  The mean-vector
-- coherence statistic is an exploratory ~3.49% upper-tail observation, but it
-- was selected alongside other diagnostics and is not promoted to a
-- confirmatory p-value, Monster selector, Moonshine theorem, or RH evidence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix

------------------------------------------------------------------------
-- 1. Exact finite combinatorial / executable receipt.
------------------------------------------------------------------------

oggPrimeCount : Nat
oggPrimeCount = 15

nonOggControlCount : Nat
nonOggControlCount = 5

combinedPrimeCount : Nat
combinedPrimeCount = 20

balancedAssignmentCount : Nat
balancedAssignmentCount = 15504

energyLowerOrEqualCount : Nat
energyLowerOrEqualCount = 3459

energyUpperOrEqualCount : Nat
energyUpperOrEqualCount = 12046

coherenceLowerOrEqualCount : Nat
coherenceLowerOrEqualCount = 14964

coherenceUpperOrEqualCount : Nat
coherenceUpperOrEqualCount = 541

zeroSampleCount : Nat
zeroSampleCount = 849

phaseControlProducerPath : String
phaseControlProducerPath = "scripts/monster_climbing_gym_phase_control.py"

phaseObservableLabel : String
phaseObservableLabel =
  "C(t)=sum_{p in Ogg15} exp(i*t*log p)-3*sum_{q in nonOgg5} exp(i*t*log q)"

energyStatisticLabel : String
energyStatisticLabel = "mean_t |C(t)|^2"

meanVectorStatisticLabel : String
meanVectorStatisticLabel = "|mean_t C(t)|"

------------------------------------------------------------------------
-- 2. The five controls are the independently typed non-Ogg rows already on
-- master, not controls invented after seeing this phase statistic.
------------------------------------------------------------------------

control37IsNonOgg : Matrix.externalOggLabel Matrix.prime37 ≡ false
control37IsNonOgg = Matrix.prime37ExternallyNegative

control43IsNonOgg : Matrix.externalOggLabel Matrix.prime43 ≡ false
control43IsNonOgg = Matrix.prime43ExternallyNegative

control53IsNonOgg : Matrix.externalOggLabel Matrix.prime53 ≡ false
control53IsNonOgg = Matrix.prime53ExternallyNegative

control61IsNonOgg : Matrix.externalOggLabel Matrix.prime61 ≡ false
control61IsNonOgg = Matrix.prime61ExternallyNegative

control67IsNonOgg : Matrix.externalOggLabel Matrix.prime67 ≡ false
control67IsNonOgg = Matrix.prime67ExternallyNegative

------------------------------------------------------------------------
-- 3. Claim boundary.
------------------------------------------------------------------------

record ClimbingGymPhaseControlBoundary : Set where
  constructor climbing-gym-phase-control-boundary
  field
    same849ZeroCacheUsed : Bool
    allBalancedFiveControlAssignmentsEnumerated : Bool
    randomSeedRequired : Bool
    existingNonOggControlMatrixReused : Bool
    centeredCoefficientContrastUsed : Bool
    energyStatisticMonsterSpecific : Bool
    meanVectorCoherenceUpperTailObserved : Bool
    meanVectorCoherencePromotedConfirmatory : Bool
    multipleStatisticSelectionWarning : Bool
    phaseControlProvesMoonshine : Bool
    phaseControlProvesRiemannHypothesis : Bool

open ClimbingGymPhaseControlBoundary public

canonicalClimbingGymPhaseControlBoundary : ClimbingGymPhaseControlBoundary
canonicalClimbingGymPhaseControlBoundary =
  climbing-gym-phase-control-boundary
    true
    true
    false
    true
    true
    false
    true
    false
    true
    false
    false
