module DASHI.Physics.Closure.NSTriadKNDefectFailureThresholdCrossingRound254Exact where

------------------------------------------------------------------------
-- ROUND254 / DEFECT-BUDGET FAILURE -> ACTUAL THRESHOLD-CROSSING SEQUENCE
--
-- Constructively, the contrapositive estimate alone gives only a negation of
-- a global barrier.  To feed R242 we need an actual selected cutoff and time.
-- This file isolates exactly that classical/analytic selection step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242

record DefectFailureThresholdSelector
    (Time : Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ) : Set₁ where
  field
    selectedCutoff : Nat → Nat
    selectedCrossing :
      (n : Nat) →
      R242.ThresholdCrossing
        Time criticalSize threshold (selectedCutoff n)

open DefectFailureThresholdSelector public

selectorProducesCrossingFamily :
  ∀ {Time criticalSize threshold}
    (S : DefectFailureThresholdSelector Time criticalSize threshold) →
  (n : Nat) →
  R242.ThresholdCrossing
    Time criticalSize threshold (selectedCutoff S n)
selectorProducesCrossingFamily S = selectedCrossing S

round254ThresholdCrossingConsumerShapeClosed : Bool
round254ThresholdCrossingConsumerShapeClosed = true

round254ConstructiveContrapositiveAloneSelectsWitnesses : Bool
round254ConstructiveContrapositiveAloneSelectsWitnesses = false

round254ClassicalOrAnalyticSelectionStillSourceOwned : Bool
round254ClassicalOrAnalyticSelectionStillSourceOwned = true

round254PackageAClosed : Bool
round254PackageAClosed = false

round254ThresholdCrossingConsumerShapeClosedIsTrue :
  round254ThresholdCrossingConsumerShapeClosed ≡ true
round254ThresholdCrossingConsumerShapeClosedIsTrue = refl

round254ConstructiveContrapositiveAloneSelectsWitnessesIsFalse :
  round254ConstructiveContrapositiveAloneSelectsWitnesses ≡ false
round254ConstructiveContrapositiveAloneSelectsWitnessesIsFalse = refl
