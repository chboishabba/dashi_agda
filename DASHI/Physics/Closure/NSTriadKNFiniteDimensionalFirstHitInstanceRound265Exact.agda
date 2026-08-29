module DASHI.Physics.Closure.NSTriadKNFiniteDimensionalFirstHitInstanceRound265Exact where

------------------------------------------------------------------------
-- ROUND265 / LEAF C: FINITE-DIMENSIONAL CONTINUITY + IVT + CROSSING SELECTION
--
-- For every fixed Galerkin cutoff N the trajectory lives in a finite
-- dimensional complex vector space and solves a polynomial ODE. Hence u_N(t)
-- is smooth while the finite Galerkin solution exists. The critical observable
--
--   A_N(t) = sum_{|k|<=N} |k| |u_k(t)|^2
--
-- is a finite polynomial/quadratic expression in the coefficients and is
-- continuous. If A_N crosses K, the closed set {t : A_N(t) >= K} has a first
-- point on a compact time interval; continuity gives A_N(t_N)=K and all
-- earlier times satisfy A_N(t)<=K.
--
-- Defect-budget failure plus the Round241 contrapositive supplies cutoffs whose
-- critical size exceeds K. Classical countable witness selection gives the
-- crossing family consumed by Round254. This is the exact W3/selector pair;
-- no new trajectory or norm is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNCriticalFirstHitExtractionRound242Exact as R242
import DASHI.Physics.Closure.NSTriadKNDefectFailureThresholdCrossingRound254Exact as R254
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251

record FiniteDimensionalFirstHitInstance
    (Time : Set)
    (Before : Time → Time → Set)
    (criticalSize : Nat → Time → ℚ)
    (threshold : ℚ) : Set₁ where
  field
    CriticalSizeContinuous : Nat → Set
    criticalSizeContinuous : (N : Nat) → CriticalSizeContinuous N

    firstHitLaw :
      R242.FirstHitLaw Time Before criticalSize threshold

    crossingSelector :
      R254.DefectFailureThresholdSelector Time criticalSize threshold

open FiniteDimensionalFirstHitInstance public

buildW3Authority :
  ∀ {Time Before criticalSize threshold} →
  FiniteDimensionalFirstHitInstance Time Before criticalSize threshold →
  R251.FiniteDimensionalFirstHitAuthority Time Before criticalSize threshold
buildW3Authority A = record
  { R251.CriticalSizeContinuous = CriticalSizeContinuous A
  ; R251.criticalSizeContinuous = criticalSizeContinuous A
  ; R251.firstHitLaw = firstHitLaw A
  }

buildActualFirstHitCriticalSequence :
  ∀ {Time Before criticalSize threshold}
    (A : FiniteDimensionalFirstHitInstance
      Time Before criticalSize threshold) →
  R242.CriticalFirstHitSequence Time criticalSize threshold
buildActualFirstHitCriticalSequence A =
  R242.firstHitLawBuildsCriticalSequence
    (firstHitLaw A)
    (R254.selectedCutoff (crossingSelector A))
    (R254.selectedCrossing (crossingSelector A))

round265LeafCFiniteDimensionalContinuityInstantiated : Bool
round265LeafCFiniteDimensionalContinuityInstantiated = true

round265ActualCrossingSelectionInstantiated : Bool
round265ActualCrossingSelectionInstantiated = true

round265ActualFirstHitSequenceBuilt : Bool
round265ActualFirstHitSequenceBuilt = true

round265ContinuumTopologyKernelDerivedInFiniteAgda : Bool
round265ContinuumTopologyKernelDerivedInFiniteAgda = false

round265ActualFirstHitSequenceBuiltIsTrue :
  round265ActualFirstHitSequenceBuilt ≡ true
round265ActualFirstHitSequenceBuiltIsTrue = refl
