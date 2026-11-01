module DASHI.Physics.Foundations.CabarlahGoniometerDirectionFindingCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahSignalInferenceExact as Cabarlah
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as DirectionFinding

------------------------------------------------------------------------
-- Cross-pollination adapter kept separate from the established Cabarlah owner
-- so the new DF surface does not rewrite prior source-bounded claims.

goniometricBearingCollision : DirectionFinding.SameBearingCollision
goniometricBearingCollision = DirectionFinding.canonicalSameBearingCollision

goniometricBearingDoesNotDetermineExactWorld :
  ¬ DirectionFinding.BearingDeterminesExactEmitterWorld
goniometricBearingDoesNotDetermineExactWorld =
  DirectionFinding.bearingDoesNotDetermineExactEmitterWorld

goniometricObservationDoesNotAuthoriseMilitaryAction :
  DirectionFinding.goniometricObservationAuthorisesMilitaryAction
    DirectionFinding.canonicalDirectionFindingBoundary
  ≡ false
goniometricObservationDoesNotAuthoriseMilitaryAction = refl

mechanicalAndElectronicDFShareRoleNotImplementation :
  DirectionFinding.implementationRole DirectionFinding.mechanicalAngleReadout
  ≡ DirectionFinding.implementationRole DirectionFinding.phaseComparison
mechanicalAndElectronicDFShareRoleNotImplementation = refl

mechanicalAndPhaseImplementationsRemainDistinct :
  DirectionFinding.mechanicalAngleReadout
  ≡ DirectionFinding.phaseComparison → ⊥
mechanicalAndPhaseImplementationsRemainDistinct =
  DirectionFinding.mechanicalAngleReadoutIsNotPhaseComparison

-- The existing Cabarlah non-injectivity remains available alongside the new
-- direction-finding collision; neither observation route is silently promoted
-- to exact emitting-world recovery.

cabarlahSignalInferenceRemainsNonInjective : ¬ Cabarlah.SignalInferenceInjective
cabarlahSignalInferenceRemainsNonInjective = Cabarlah.signalInferenceIsNotInjective
