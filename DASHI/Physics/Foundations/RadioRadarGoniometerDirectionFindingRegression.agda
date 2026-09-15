module DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as G

------------------------------------------------------------------------
-- RED-first contract for the goniometer / direction-finding owner.
-- This regression is intentionally written against the desired public surface
-- before the production module exists.

record RadioRadarGoniometerDirectionFindingRegression : Set where
  constructor regression
  field
    mechanical-role : G.AngleMeasurementRole
    phase-role : G.AngleMeasurementRole
    amplitude-role : G.AngleMeasurementRole
    monopulse-role : G.AngleMeasurementRole
    beamforming-role : G.AngleMeasurementRole

    same-bearing-collision : G.SameBearingCollision
    bearing-not-exact-world : ¬ G.BearingDeterminesExactEmitterWorld

    mechanical-not-modern-phase :
      G.mechanicalAngleReadout ≡ G.phaseComparison → ⊥

    observation-does-not-authorise-action :
      G.goniometricObservationAuthorisesMilitaryAction
      G.canonicalDirectionFindingBoundary
      ≡ false

canonicalRegression : RadioRadarGoniometerDirectionFindingRegression
canonicalRegression =
  regression
    G.angleEstimationRole
    G.angleEstimationRole
    G.angleEstimationRole
    G.angleEstimationRole
    G.angleEstimationRole
    G.canonicalSameBearingCollision
    G.bearingDoesNotDetermineExactEmitterWorld
    G.mechanicalAngleReadoutIsNotPhaseComparison
    refl
