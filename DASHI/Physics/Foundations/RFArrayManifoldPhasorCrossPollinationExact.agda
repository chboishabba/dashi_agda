module DASHI.Physics.Foundations.RFArrayManifoldPhasorCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Foundations.RFArrayManifoldSourceAtlasExact as Sources
import DASHI.Physics.Foundations.RFComplexSmithPhasedArrayGoniometerExact as ComplexRF
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer

------------------------------------------------------------------------
-- PHASOR -> SPATIALLY RELATIVE PHASE
--
-- This finite witness deliberately omits deployment geometry.  It establishes
-- only the information distinction needed by the existing observer calculus:
-- equal scalar magnitude can coexist with different spatial phase and hence
-- different angular observations.
------------------------------------------------------------------------

data ArrayWorld : Set where
  worldPhaseA : ArrayWorld
  worldPhaseB : ArrayWorld

data ScalarMagnitudeObservation : Set where
  sameMagnitude : ScalarMagnitudeObservation

data SpatialRelativePhaseObservation : Set where
  phaseA : SpatialRelativePhaseObservation
  phaseB : SpatialRelativePhaseObservation

observeMagnitude : ArrayWorld → ScalarMagnitudeObservation
observeMagnitude _ = sameMagnitude

observeSpatialPhase : ArrayWorld → SpatialRelativePhaseObservation
observeSpatialPhase worldPhaseA = phaseA
observeSpatialPhase worldPhaseB = phaseB

bearingFromSpatialPhase : SpatialRelativePhaseObservation → Array.ArrayBearing
bearingFromSpatialPhase phaseA = Array.bearingA
bearingFromSpatialPhase phaseB = Array.bearingB

bearingFromArrayWorld : ArrayWorld → Array.ArrayBearing
bearingFromArrayWorld world =
  bearingFromSpatialPhase (observeSpatialPhase world)

bearingAIsNotBearingB : Array.bearingA ≡ Array.bearingB → ⊥
bearingAIsNotBearingB ()

MagnitudeFactorsToBearing : Set
MagnitudeFactorsToBearing =
  Σ (ScalarMagnitudeObservation → Array.ArrayBearing) λ recover →
    (world : ArrayWorld) →
    recover (observeMagnitude world) ≡ bearingFromArrayWorld world

magnitudeAloneDoesNotRecoverBearing : ¬ MagnitudeFactorsToBearing
magnitudeAloneDoesNotRecoverBearing (recover , factors) =
  bearingAIsNotBearingB
    (trans
      (sym (factors worldPhaseA))
      (factors worldPhaseB))

record PhasorSpatialPhaseReceipt : Set where
  constructor phasor-spatial-phase-receipt
  field
    complexRFReceiptRetained : ComplexRF.EngineeringJReceipt
    equalMagnitudeCanHideDifferentSpatialPhase : Bool
    equalMagnitudeCanHideDifferentSpatialPhaseIsTrue :
      equalMagnitudeCanHideDifferentSpatialPhase ≡ true
    magnitudeAloneCannotPayAngularConsumer :
      ¬ MagnitudeFactorsToBearing
    relativeSpatialPhaseFeedsAngularObservation : Bool
    relativeSpatialPhaseFeedsAngularObservationIsTrue :
      relativeSpatialPhaseFeedsAngularObservation ≡ true
open PhasorSpatialPhaseReceipt public

canonicalPhasorSpatialPhaseReceipt : PhasorSpatialPhaseReceipt
canonicalPhasorSpatialPhaseReceipt =
  phasor-spatial-phase-receipt
    ComplexRF.canonicalEngineeringJReceipt
    true refl
    magnitudeAloneDoesNotRecoverBearing
    true refl

------------------------------------------------------------------------
-- ARRAY MANIFOLD
--
-- Belloni et al. separate array-dependent structure from wavefield-dependent
-- structure.  The constructors below retain that source-paid distinction as
-- typed coordinates without claiming a complete electromagnetic model.
------------------------------------------------------------------------

data ArrayManifoldCoordinate : Set where
  arrayDependentCoordinate : ArrayManifoldCoordinate
  wavefieldDependentCoordinate : ArrayManifoldCoordinate
  electromagneticCorrectionCoordinate : ArrayManifoldCoordinate

arrayDependentIsNotWavefieldDependent :
  arrayDependentCoordinate ≡ wavefieldDependentCoordinate → ⊥
arrayDependentIsNotWavefieldDependent ()

record ArrayManifoldReceipt : Set where
  constructor array-manifold-receipt
  field
    godaraReviewRetained :
      Snowball.SourceRoleSnowballReceipt Sources.godaraArrayReview
    belloniManifoldRetained :
      Snowball.SourceRoleSnowballReceipt Sources.belloniManifoldSeparation
    electromagneticManifoldRetained :
      Snowball.SourceRoleSnowballReceipt Sources.electromagneticManifoldPrimary
    keysightPrimerRetained :
      Snowball.SourceRoleSnowballReceipt Sources.keysightPhasedArrayPrimer

    arrayAndWavefieldCoordinatesRemainDistinct :
      arrayDependentCoordinate ≡ wavefieldDependentCoordinate → ⊥

    manifoldSupportsAngularConsumer : Bool
    manifoldSupportsAngularConsumerIsTrue :
      manifoldSupportsAngularConsumer ≡ true

    manifoldIsExactHardwareIdentity : Bool
    manifoldIsExactHardwareIdentityIsFalse :
      manifoldIsExactHardwareIdentity ≡ false

    manifoldDeterminesExactEmitterWorld : Bool
    manifoldDeterminesExactEmitterWorldIsFalse :
      manifoldDeterminesExactEmitterWorld ≡ false

open ArrayManifoldReceipt public

canonicalArrayManifoldReceipt : ArrayManifoldReceipt
canonicalArrayManifoldReceipt =
  array-manifold-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.godaraArrayReview)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.belloniManifoldSeparation)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.electromagneticManifoldPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.keysightPhasedArrayPrimer)
    arrayDependentIsNotWavefieldDependent
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- DIFFERENT CONSUMERS OF RELATED ARRAY COORDINATES
------------------------------------------------------------------------

data ArrayConsumer : Set where
  beamformingConsumer : ArrayConsumer
  directionFindingConsumer : ArrayConsumer

record ArrayConsumerRoleReceipt : Set where
  constructor array-consumer-role-receipt
  field
    phasedArrayAngularRoleRetained :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole
    interferometricAngularRoleRetained :
      Array.supportsAngularObservation Array.phaseComparisonInterferometer
      ≡ Array.angularObservationRole

    sharedArrayCoordinatesImplySameConsumer : Bool
    sharedArrayCoordinatesImplySameConsumerIsFalse :
      sharedArrayCoordinatesImplySameConsumer ≡ false

    beamformingEqualsDirectionFinding : Bool
    beamformingEqualsDirectionFindingIsFalse :
      beamformingEqualsDirectionFinding ≡ false

    angularObservationEqualsBeamSteering : Bool
    angularObservationEqualsBeamSteeringIsFalse :
      angularObservationEqualsBeamSteering ≡ false

open ArrayConsumerRoleReceipt public

canonicalArrayConsumerRoleReceipt : ArrayConsumerRoleReceipt
canonicalArrayConsumerRoleReceipt =
  array-consumer-role-receipt
    refl
    refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- GONIOMETER ENDPOINT
------------------------------------------------------------------------

record ArrayManifoldGoniometerEndpoint : Set where
  constructor array-manifold-goniometer-endpoint
  field
    modernPhaseComparisonCarriesAngleRole :
      Goniometer.implementationRole Goniometer.phaseComparison
      ≡ Goniometer.angleEstimationRole

    mechanicalGoniometerCarriesAngleRole :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole

    manifoldAndGoniometerShareOnlyAbstractAngularRole : Bool
    manifoldAndGoniometerShareOnlyAbstractAngularRoleIsTrue :
      manifoldAndGoniometerShareOnlyAbstractAngularRole ≡ true

    arrayManifoldEqualsMechanicalGoniometerHardware : Bool
    arrayManifoldEqualsMechanicalGoniometerHardwareIsFalse :
      arrayManifoldEqualsMechanicalGoniometerHardware ≡ false

open ArrayManifoldGoniometerEndpoint public

canonicalArrayManifoldGoniometerEndpoint : ArrayManifoldGoniometerEndpoint
canonicalArrayManifoldGoniometerEndpoint =
  array-manifold-goniometer-endpoint
    refl
    refl
    true refl
    false refl

------------------------------------------------------------------------
-- SMITH-CHART SIBLING FIREWALL
--
-- Smith coordinates describe impedance/reflection at RF ports.  Array
-- manifolds describe spatial response structure.  Both are complex-RF
-- coordinate families, but one is not a substitute for the other.
------------------------------------------------------------------------

record SmithAoAFirewall : Set where
  constructor smith-aoa-firewall
  field
    smithCoordinateReceiptRetained : ComplexRF.SmithChartCoordinateReceipt

    smithChartComputesArrayBearing : Bool
    smithChartComputesArrayBearingIsFalse :
      smithChartComputesArrayBearing ≡ false

    impedanceMatchingEqualsDirectionFinding : Bool
    impedanceMatchingEqualsDirectionFindingIsFalse :
      impedanceMatchingEqualsDirectionFinding ≡ false

    sParameterEqualsArrayManifold : Bool
    sParameterEqualsArrayManifoldIsFalse :
      sParameterEqualsArrayManifold ≡ false

    sharedComplexArithmeticImpliesSamePhysicalObservable : Bool
    sharedComplexArithmeticImpliesSamePhysicalObservableIsFalse :
      sharedComplexArithmeticImpliesSamePhysicalObservable ≡ false

open SmithAoAFirewall public

canonicalSmithAoAFirewall : SmithAoAFirewall
canonicalSmithAoAFirewall =
  smith-aoa-firewall
    ComplexRF.canonicalSmithChartCoordinateReceipt
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- EXISTING NON-INJECTIVITY REMAINS THE TERMINAL WORLD-RECOVERY BOUNDARY
------------------------------------------------------------------------

arrayBearingStillDoesNotDetermineExactEmitterWorld :
  ¬ Array.ArrayBearingDeterminesExactEmitterWorld
arrayBearingStillDoesNotDetermineExactEmitterWorld =
  Array.arrayBearingDoesNotDetermineExactEmitterWorld

goniometerBearingStillDoesNotDetermineExactEmitterWorld :
  ¬ Goniometer.BearingDeterminesExactEmitterWorld
goniometerBearingStillDoesNotDetermineExactEmitterWorld =
  Goniometer.bearingDoesNotDetermineExactEmitterWorld
