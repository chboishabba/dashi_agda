module DASHI.Physics.Closure.NSTriadKNMixedDefectAlmostPeriodicDynamicsRound272Exact where

------------------------------------------------------------------------
-- ROUND272 / DYNAMIC WELD AUDIT FOR THE MIXED-DEFECT CRITICAL ELEMENT
--
-- R271 selects bounded first-hit profiles.  A first attempt at the dynamic
-- weld asked for one maximal-lifespan nonlinear solution whose renormalized
-- orbit is precompact in critical H^(1/2) while mixed-defect badness persists.
--
-- ROUND281 CORRECTION.
-- H^(1/2) is invariant under the Navier--Stokes translation/scaling symmetry.
-- Hence precompactness modulo those symmetries implies a finite critical-norm
-- bound.  But R241 + the installed W1/W2 lane already pays the mixed defect on
-- every finite critical barrier with finite integrated dissipation.  Therefore
-- a globally bounded almost-periodic solution cannot simultaneously remain a
-- persistent mixed-defect-bad object.
--
-- The correct dynamic inverse-extraction target must retain the threshold
-- escape rather than collapse it to one bounded critical orbit:
--
--   bad cutoff family
--     -> increasing thresholds K_m
--     -> first-hit states u_{N_m}(t_m) with ||u||_{H^(1/2)}^2 = K_m
--     -> threshold-indexed nonlinear/profile geometry
--     -> a contradiction or direct uniform barrier.
--
-- Alternatively one returns to the direct quartic-companion / signed
-- covariance route, whose purpose is precisely to establish the barrier that
-- R241 would then consume.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ThresholdEscapingMixedDefectDynamics {ℓ : Level}
    (State : Set ℓ) : Set (lsuc ℓ) where
  field
    Threshold : Set ℓ
    Time : Set ℓ

    selectedState : Threshold → State
    selectedTime : Threshold → Time
    selectedCriticalSizeEqualsThreshold : Set ℓ
    thresholdsEscapeEveryFiniteBarrier : Set ℓ

    eachSelectedStateComesFromSamePhysicalGalerkinFamily : Set ℓ
    nonlinearEvolutionFromEachSelectedState : Set ℓ
    profileGeometryCompatibleAcrossThresholds : Set ℓ

    noSingleUniformCriticalBoundAssumed : Set ℓ

open ThresholdEscapingMixedDefectDynamics public

round272StaticR271ProfileIsNotYetDynamicSolution : Bool
round272StaticR271ProfileIsNotYetDynamicSolution = true

round272BoundedAlmostPeriodicPersistentBadTargetRejected : Bool
round272BoundedAlmostPeriodicPersistentBadTargetRejected = true

round272CorrectTargetRetainsThresholdEscape : Bool
round272CorrectTargetRetainsThresholdEscape = true

round272ThresholdEscapingDynamicExtractionClosed : Bool
round272ThresholdEscapingDynamicExtractionClosed = false

round272PackageAClosed : Bool
round272PackageAClosed = false

round272BoundedAlmostPeriodicPersistentBadTargetRejectedIsTrue :
  round272BoundedAlmostPeriodicPersistentBadTargetRejected ≡ true
round272BoundedAlmostPeriodicPersistentBadTargetRejectedIsTrue = refl

round272ThresholdEscapingDynamicExtractionClosedIsFalse :
  round272ThresholdEscapingDynamicExtractionClosed ≡ false
round272ThresholdEscapingDynamicExtractionClosedIsFalse = refl
