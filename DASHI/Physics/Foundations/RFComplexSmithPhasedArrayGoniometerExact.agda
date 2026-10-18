module DASHI.Physics.Foundations.RFComplexSmithPhasedArrayGoniometerExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.JInvariantSourceAtlasExact as ModularJ
import DASHI.Physics.Foundations.RFComplexSmithSourceAtlasExact as Sources
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer

------------------------------------------------------------------------
-- ELECTRICAL-ENGINEERING j
--
-- In this owner, engineering j is exactly the existing complex imaginary
-- unit.  The modular j-invariant lives in a different semantic/source lane.
------------------------------------------------------------------------

engineeringJ : ∀ {R} → Complex.ComplexPair R
engineeringJ = Complex.imaginaryUnit

engineeringJIsImaginaryUnit :
  ∀ {R} → engineeringJ {R} ≡ Complex.imaginaryUnit
engineeringJIsImaginaryUnit = refl

data JSymbolMeaning : Set where
  engineeringImaginaryUnitMeaning : JSymbolMeaning
  modularJInvariantMeaning : JSymbolMeaning

engineeringJMeaningDistinctFromModularJMeaning :
  engineeringImaginaryUnitMeaning ≡ modularJInvariantMeaning → ⊥
engineeringJMeaningDistinctFromModularJMeaning ()

record EngineeringJReceipt : Set where
  constructor engineering-j-receipt
  field
    engineeringJUsesComplexImaginaryUnit : Bool
    engineeringJUsesComplexImaginaryUnitIsTrue :
      engineeringJUsesComplexImaginaryUnit ≡ true
    engineeringJNotationSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.engineeringJNotationSource
open EngineeringJReceipt public

canonicalEngineeringJReceipt : EngineeringJReceipt
canonicalEngineeringJReceipt =
  engineering-j-receipt
    true refl
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.engineeringJNotationSource)

------------------------------------------------------------------------
-- SMITH-CHART / REFLECTION-COEFFICIENT COORDINATES
--
-- The source atlas pays the analytic engineering relationship.  The finite
-- classes below are a DASHI synthetic witness that impedance and reflection
-- coordinates are distinct representations and that reactive sign survives.
------------------------------------------------------------------------

data NormalizedImpedanceClass : Set where
  matchedImpedance : NormalizedImpedanceClass
  inductiveImpedance : NormalizedImpedanceClass
  capacitiveImpedance : NormalizedImpedanceClass

data ReflectionCoefficientClass : Set where
  zeroReflection : ReflectionCoefficientClass
  upperHalfReflection : ReflectionCoefficientClass
  lowerHalfReflection : ReflectionCoefficientClass

smithProjection :
  NormalizedImpedanceClass → ReflectionCoefficientClass
smithProjection matchedImpedance = zeroReflection
smithProjection inductiveImpedance = upperHalfReflection
smithProjection capacitiveImpedance = lowerHalfReflection

upperAndLowerReflectionDistinct :
  upperHalfReflection ≡ lowerHalfReflection → ⊥
upperAndLowerReflectionDistinct ()

data RFPortObservationCoordinate : Set where
  complexImpedanceCoordinate : RFPortObservationCoordinate
  reflectionCoefficientCoordinate : RFPortObservationCoordinate
  sParameterCoordinate : RFPortObservationCoordinate
  phasorMagnitudeCoordinate : RFPortObservationCoordinate
  phasorPhaseCoordinate : RFPortObservationCoordinate

record SmithChartCoordinateReceipt : Set where
  constructor smith-chart-coordinate-receipt
  field
    keysightSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.keysightSmithChartSource
    rohdeSmithSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.rohdeSmithChartSource
    rohdeSParameterSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.rohdeSParameterSource
    matchedMapsToZeroReflection :
      smithProjection matchedImpedance ≡ zeroReflection
    inductiveAndCapacitiveRemainDistinguishable :
      upperHalfReflection ≡ lowerHalfReflection → ⊥
    smithChartCoordinateEqualsPhysicalHardware : Bool
    smithChartCoordinateEqualsPhysicalHardwareIsFalse :
      smithChartCoordinateEqualsPhysicalHardware ≡ false
open SmithChartCoordinateReceipt public

canonicalSmithChartCoordinateReceipt : SmithChartCoordinateReceipt
canonicalSmithChartCoordinateReceipt =
  smith-chart-coordinate-receipt
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.keysightSmithChartSource)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.rohdeSmithChartSource)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.rohdeSParameterSource)
    refl
    upperAndLowerReflectionDistinct
    false refl

------------------------------------------------------------------------
-- PHASOR -> ARRAY CROSS-POLLINATION
--
-- Complex RF phase and the array's relative-phase observation coordinate are
-- connected only at the observation-role level.  A Smith-chart coordinate is
-- not itself a bearing, and an S-parameter is not an emitter identity.
------------------------------------------------------------------------

record PhasorArrayCrossPollinationReceipt : Set where
  constructor phasor-array-cross-pollination-receipt
  field
    complexPhaseCoordinateRetained : Bool
    complexPhaseCoordinateRetainedIsTrue :
      complexPhaseCoordinateRetained ≡ true
    arrayRelativePhaseCoordinateRetained :
      Array.relativePhaseCoordinate ≡ Array.relativePhaseCoordinate
    phaseComparisonArrayCarriesAngularRole :
      Array.supportsAngularObservation Array.phaseComparisonInterferometer
      ≡ Array.angularObservationRole
    electronicPhasedArrayCarriesAngularRole :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole
    smithChartObservationEqualsArrayBearing : Bool
    smithChartObservationEqualsArrayBearingIsFalse :
      smithChartObservationEqualsArrayBearing ≡ false
    complexPortObservationDeterminesExactEmitterWorld : Bool
    complexPortObservationDeterminesExactEmitterWorldIsFalse :
      complexPortObservationDeterminesExactEmitterWorld ≡ false
open PhasorArrayCrossPollinationReceipt public

canonicalPhasorArrayCrossPollinationReceipt :
  PhasorArrayCrossPollinationReceipt
canonicalPhasorArrayCrossPollinationReceipt =
  phasor-array-cross-pollination-receipt
    true refl
    refl
    refl
    refl
    false refl
    false refl

------------------------------------------------------------------------
-- GONIOMETER ENDPOINT
--
-- Modern phase-sensitive RF observations and the historical/mechanical
-- goniometer can inhabit the same abstract angle-estimation role without
-- becoming the same hardware implementation.
------------------------------------------------------------------------

record GoniometerComplexPhaseEndpointReceipt : Set where
  constructor goniometer-complex-phase-endpoint-receipt
  field
    phaseComparisonCarriesGoniometerAngleRole :
      Goniometer.implementationRole Goniometer.phaseComparison
      ≡ Goniometer.angleEstimationRole
    mechanicalReadoutCarriesGoniometerAngleRole :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole
    phasedArrayAndMechanicalGoniometerSameHardware : Bool
    phasedArrayAndMechanicalGoniometerSameHardwareIsFalse :
      phasedArrayAndMechanicalGoniometerSameHardware ≡ false
    commonAngleRoleDeterminesExactEmitterWorld : Bool
    commonAngleRoleDeterminesExactEmitterWorldIsFalse :
      commonAngleRoleDeterminesExactEmitterWorld ≡ false
open GoniometerComplexPhaseEndpointReceipt public

canonicalGoniometerComplexPhaseEndpointReceipt :
  GoniometerComplexPhaseEndpointReceipt
canonicalGoniometerComplexPhaseEndpointReceipt =
  goniometer-complex-phase-endpoint-receipt
    refl
    refl
    false refl
    false refl

------------------------------------------------------------------------
-- MODULAR-j FIREWALL
--
-- Import the existing modular-j attribution lane only to make the semantic
-- non-identification explicit.  No modular-j theorem is imported into RF.
------------------------------------------------------------------------

record EngineeringJModularJFirewall : Set where
  constructor engineering-j-modular-j-firewall
  field
    symbolMeaningsDistinct :
      engineeringImaginaryUnitMeaning ≡ modularJInvariantMeaning → ⊥
    modularJSourceAtlasExists : Bool
    modularJSourceAtlasExistsIsTrue : modularJSourceAtlasExists ≡ true
    electricalJEqualsModularJInvariant : Bool
    electricalJEqualsModularJInvariantIsFalse :
      electricalJEqualsModularJInvariant ≡ false
    smithChartIsModularCurve : Bool
    smithChartIsModularCurveIsFalse : smithChartIsModularCurve ≡ false
    sharedComplexPlaneLanguageImportsModularProof : Bool
    sharedComplexPlaneLanguageImportsModularProofIsFalse :
      sharedComplexPlaneLanguageImportsModularProof ≡ false
open EngineeringJModularJFirewall public

canonicalEngineeringJModularJFirewall : EngineeringJModularJFirewall
canonicalEngineeringJModularJFirewall =
  engineering-j-modular-j-firewall
    engineeringJMeaningDistinctFromModularJMeaning
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing non-injectivity survives the new coordinate layer.
------------------------------------------------------------------------

arrayBearingStillDoesNotDetermineExactEmitterWorld :
  ¬ Array.ArrayBearingDeterminesExactEmitterWorld
arrayBearingStillDoesNotDetermineExactEmitterWorld =
  Array.arrayBearingDoesNotDetermineExactEmitterWorld

goniometerBearingStillDoesNotDetermineExactEmitterWorld :
  ¬ Goniometer.BearingDeterminesExactEmitterWorld
goniometerBearingStillDoesNotDetermineExactEmitterWorld =
  Goniometer.bearingDoesNotDetermineExactEmitterWorld
