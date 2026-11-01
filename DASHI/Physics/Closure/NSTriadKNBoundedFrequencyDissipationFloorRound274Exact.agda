module DASHI.Physics.Closure.NSTriadKNBoundedFrequencyDissipationFloorRound274Exact where

------------------------------------------------------------------------
-- ROUND274 / BOUNDED-FREQUENCY COMPACT ORBIT -> POSITIVE DISSIPATION FLOOR
--
-- BIDI proof shape:
--   renormalized H^(1/2)-orbit precompact
-- + zero excluded from orbit closure
-- + frequency scale bounded above and below away from zero
-- + continuity of the H^1/gradient observable on the compact normalized orbit
-- ---------------------------------------------------------------------------
--   inf_t ||grad u_c(t)||_2^2 > 0.
--
-- The zero-exclusion and scale lower bound are explicit.  Without them,
-- compactness alone does not give a positive floor.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record BoundedFrequencyPositiveDissipationFloor {ℓ : Level}
    (CriticalDynamics : Set ℓ) : Set (lsuc ℓ) where
  field
    dynamics : CriticalDynamics

    normalizedOrbitCompact : Set ℓ
    zeroExcludedFromOrbitClosure : Set ℓ
    frequencyScaleBoundedBelowAwayFromZero : Set ℓ
    frequencyScaleBoundedAbove : Set ℓ

    gradientObservableContinuousOnNormalizedOrbit : Set ℓ
    zeroGradientImpliesZeroNormalizedState : Set ℓ

    PositiveFloor : Set ℓ
    positiveGradientFloorOnWholeGlobalOrbit : Set ℓ

open BoundedFrequencyPositiveDissipationFloor public

round274CompactnessAloneDoesNotImplyPositiveFloor : Bool
round274CompactnessAloneDoesNotImplyPositiveFloor = true

round274ZeroExclusionAndScaleBoundsAreBinding : Bool
round274ZeroExclusionAndScaleBoundsAreBinding = true

round274PositiveDissipationFloorClosed : Bool
round274PositiveDissipationFloorClosed = false

round274PackageAClosed : Bool
round274PackageAClosed = false

round274PositiveDissipationFloorClosedIsFalse : round274PositiveDissipationFloorClosed ≡ false
round274PositiveDissipationFloorClosedIsFalse = refl
