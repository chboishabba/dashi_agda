module DASHI.Physics.Spectroscopy.MaiwaldMathieuStabilityAndActionResponseCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Source-shaped QIT and action-spectroscopy response owner.

data TrapAxis : Set where radial axial : TrapAxis

data StabilityState : Set where stable unstable boundary : StabilityState

record MathieuCoordinate : Set where
  constructor mathieu-coordinate
  field
    axis : TrapAxis
    aParameter : String
    qParameter : String
    driveFrequency : String
    geometryScale : String
    chargeToMass : String
    state : StabilityState
    sourceReference : String

open MathieuCoordinate public

record QITMassInferenceReceipt : Set where
  constructor qit-mass-inference-receipt
  field
    operatingPoint : MathieuCoordinate
    calibratedScanVariable : String
    observedEjectionOrResponse : String
    inferredMassToCharge : String
    calibrationStandard : String
    fragmentationModel : String

open QITMassInferenceReceipt public

record ActionResponseReceipt : Set where
  constructor action-response-receipt
  field
    irradiationFrequency : String
    photonFlux : String
    absorptionProbability : String
    tagDissociationProbability : String
    fragmentDetectionEfficiency : String
    measuredActionYield : String
    referenceSpectrum : String

open ActionResponseReceipt public

record MaiwaldResponseBoundary : Set where
  constructor maiwald-response-boundary
  field
    stableMathieuPointUniquelyDeterminesMolecule : Bool
    stableMathieuPointUniquelyDeterminesMoleculeIsFalse : stableMathieuPointUniquelyDeterminesMolecule ≡ false
    massToChargeUniquelyDeterminesStructure : Bool
    massToChargeUniquelyDeterminesStructureIsFalse : massToChargeUniquelyDeterminesStructure ≡ false
    actionYieldEqualsAbsorptionProbability : Bool
    actionYieldEqualsAbsorptionProbabilityIsFalse : actionYieldEqualsAbsorptionProbability ≡ false
    tagDissociationAndDetectionMustRemainInResponseModel : Bool
    tagDissociationAndDetectionMustRemainInResponseModelIsTrue :
      tagDissociationAndDetectionMustRemainInResponseModel ≡ true
    impactSpectrumEqualsOriginalIceGrainComposition : Bool
    impactSpectrumEqualsOriginalIceGrainCompositionIsFalse : impactSpectrumEqualsOriginalIceGrainComposition ≡ false

canonicalMaiwaldResponseBoundary : MaiwaldResponseBoundary
canonicalMaiwaldResponseBoundary =
  maiwald-response-boundary false refl false refl false refl true refl false refl
