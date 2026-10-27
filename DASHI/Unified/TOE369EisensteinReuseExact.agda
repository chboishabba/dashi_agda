{-# OPTIONS --safe #-}
module DASHI.Unified.TOE369EisensteinReuseExact where

------------------------------------------------------------------------
-- O/R/C/S/L/P/G/F
-- O: Connect existing exact Eisenstein results to the focused TOE graph.
-- R: Reuse the original biological phase and interference theorem owners.
-- C: Supply transparent theorem aliases. Do not duplicate their proofs.
-- S: Retain the physical and cardinality non-promotion boundaries.
-- L: Own only this import edge. Do not change any ESD surface.
-- P: Make existing proofs available to TOE consumers.
-- G: Keep Serge Lang (1994) and original DASHI theorem attribution.
-- F: The finite proofs below reduce to their imported theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Bool using (false)
open import Data.Rational.Base using (ℚ; 0ℚ)

import DASHI.Biology.EisensteinNineRingInterferenceExact as Ring
import DASHI.Biology.EisensteinThreeSixSymmetryExact as ThreeSix

toeEisensteinPhaseCycle :
  (phase : ThreeSix.TernaryPhase) →
  ThreeSix.nextPhase (ThreeSix.nextPhase (ThreeSix.nextPhase phase)) ≡ phase
toeEisensteinPhaseCycle = ThreeSix.threePhaseCycleCloses

toeEisensteinUnitRecovery :
  (unit : ThreeSix.EisensteinUnit) →
  ThreeSix.phaseAndOppositionDetermineUnit
    (ThreeSix.unitPhase unit) (ThreeSix.unitOpposition unit)
  ≡ unit
toeEisensteinUnitRecovery = ThreeSix.recoverUnit

toeEisensteinSixUnits :
  ThreeSix.eisensteinUnitCount ≡ 6
toeEisensteinSixUnits = ThreeSix.eisensteinUnitCountIsSix

toeEisensteinThreePhaseCancellationReal :
  Ring.realCoordinate ThreeSix.symmetricPhaseResultant ≡ 0ℚ
toeEisensteinThreePhaseCancellationReal =
  ThreeSix.symmetricPhaseResultantRealIsZero

toeEisensteinThreePhaseCancellationOmega :
  Ring.omegaCoordinate ThreeSix.symmetricPhaseResultant ≡ 0ℚ
toeEisensteinThreePhaseCancellationOmega =
  ThreeSix.symmetricPhaseResultantOmegaIsZero

toeEisensteinInterference :
  (wave : Ring.HostGuestWave) →
  Ring.joinedIntensity wave
  ≡ Ring.separateIntensity wave Data.Rational.Base._+_ Ring.interferenceContribution wave
toeEisensteinInterference = Ring.hostGuestInterferenceIdentity

toeEisensteinThreeNotOrderedScale :
  ThreeSix.ThreeSixBoundary.ternaryPhasesAreOrderedMinusZeroPlusScale
    ThreeSix.canonicalThreeSixBoundary ≡ false
toeEisensteinThreeNotOrderedScale =
  ThreeSix.ThreeSixBoundary.ternaryPhasesAreOrderedMinusZeroPlusScaleIsFalse
    ThreeSix.canonicalThreeSixBoundary

toeEisensteinNotPhysicalQuantumPhase :
  ThreeSix.ThreeSixBoundary.abstractPhaseCarrierIsPhysicalQuantumPhase
    ThreeSix.canonicalThreeSixBoundary ≡ false
toeEisensteinNotPhysicalQuantumPhase =
  ThreeSix.ThreeSixBoundary.abstractPhaseCarrierIsPhysicalQuantumPhaseIsFalse
    ThreeSix.canonicalThreeSixBoundary

toeEisensteinInterferenceNotQuantumTheory :
  Ring.EisensteinInterferenceBoundary.interferenceIdentityIsPhysicalQuantumTheory
    Ring.canonicalEisensteinInterferenceBoundary ≡ false
toeEisensteinInterferenceNotQuantumTheory =
  Ring.EisensteinInterferenceBoundary.interferenceIdentityIsPhysicalQuantumTheoryIsFalse
    Ring.canonicalEisensteinInterferenceBoundary

toeEisensteinSixCoordinatesNotDerived :
  Ring.EisensteinInterferenceBoundary.sixCoordinateReductionDerivedWithoutConstraints
    Ring.canonicalEisensteinInterferenceBoundary ≡ false
toeEisensteinSixCoordinatesNotDerived =
  Ring.EisensteinInterferenceBoundary.sixCoordinateReductionDerivedWithoutConstraintsIsFalse
    Ring.canonicalEisensteinInterferenceBoundary
