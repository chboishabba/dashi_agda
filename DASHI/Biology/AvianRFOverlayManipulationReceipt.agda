module DASHI.Biology.AvianRFOverlayManipulationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.AvianCompassSurface

------------------------------------------------------------------------
-- RF manipulation vocabulary
------------------------------------------------------------------------

data RFManipulationRole : Set where
  larmorLikeDrive : RFManipulationRole
  broadbandLikeNoise : RFManipulationRole
  staticFieldControl : RFManipulationRole
  shamFieldControl : RFManipulationRole
  pulseTrainProbe : RFManipulationRole
  frequencySweepProbe : RFManipulationRole

data InjectedFieldGeometry : Set where
  collinearInjection : InjectedFieldGeometry
  transverseInjection : InjectedFieldGeometry
  obliqueInjection : InjectedFieldGeometry
  rotatingVectorInjection : InjectedFieldGeometry
  spatialGradientInjection : InjectedFieldGeometry
  shieldedControlGeometry : InjectedFieldGeometry

data OverlayRewriteStatus : Set where
  overlayUnchanged : OverlayRewriteStatus
  overlayAxisShifted : OverlayRewriteStatus
  overlayContrastReweighted : OverlayRewriteStatus
  overlayConfidenceCollapsed : OverlayRewriteStatus
  overlayGeometryInverted : OverlayRewriteStatus
  overlayProbeObservableOnly : OverlayRewriteStatus

data BehaviorReceiptStatus : Set where
  behaviorStableControl : BehaviorReceiptStatus
  behaviorShiftedReceipt : BehaviorReceiptStatus
  behaviorRandomizedReceipt : BehaviorReceiptStatus
  behaviorRefusalReceipt : BehaviorReceiptStatus
  behaviorInversionReceipt : BehaviorReceiptStatus
  behaviorConfidenceDegradedReceipt : BehaviorReceiptStatus

data RFManipulationBoundary : Set where
  rfObservableBehaviourOnly : RFManipulationBoundary
  rfDirectVisualQualiaReadoutBlocked : RFManipulationBoundary
  rfEthicalPerturbationLicenseBlocked : RFManipulationBoundary
  rfCompleteBiophysicsClaimBlocked : RFManipulationBoundary
  rfInverseOverlayQualiaRecoveryBlocked : RFManipulationBoundary

------------------------------------------------------------------------
-- Deterministic status projections from the existing compass receipt.
------------------------------------------------------------------------

roleToPerturbationRegime : RFManipulationRole → PerturbationRegime
roleToPerturbationRegime larmorLikeDrive = oscillatingRFField
roleToPerturbationRegime broadbandLikeNoise = oscillatingRFField
roleToPerturbationRegime staticFieldControl = staticLocalMagnet
roleToPerturbationRegime shamFieldControl = noPerturbation
roleToPerturbationRegime pulseTrainProbe = oscillatingRFField
roleToPerturbationRegime frequencySweepProbe = oscillatingRFField

effectToOverlayRewrite : OrientationEffect → OverlayRewriteStatus
effectToOverlayRewrite stableHeading = overlayUnchanged
effectToOverlayRewrite shiftedHeading = overlayAxisShifted
effectToOverlayRewrite randomHeading = overlayConfidenceCollapsed
effectToOverlayRewrite refusalToOrient = overlayConfidenceCollapsed
effectToOverlayRewrite invertedCompass = overlayGeometryInverted
effectToOverlayRewrite degradedConfidence = overlayContrastReweighted

effectToBehaviorReceiptStatus : OrientationEffect → BehaviorReceiptStatus
effectToBehaviorReceiptStatus stableHeading = behaviorStableControl
effectToBehaviorReceiptStatus shiftedHeading = behaviorShiftedReceipt
effectToBehaviorReceiptStatus randomHeading = behaviorRandomizedReceipt
effectToBehaviorReceiptStatus refusalToOrient = behaviorRefusalReceipt
effectToBehaviorReceiptStatus invertedCompass = behaviorInversionReceipt
effectToBehaviorReceiptStatus degradedConfidence = behaviorConfidenceDegradedReceipt

canonicalRFBoundaries : List RFManipulationBoundary
canonicalRFBoundaries =
  rfObservableBehaviourOnly
  ∷ rfDirectVisualQualiaReadoutBlocked
  ∷ rfEthicalPerturbationLicenseBlocked
  ∷ rfCompleteBiophysicsClaimBlocked
  ∷ rfInverseOverlayQualiaRecoveryBlocked
  ∷ []

------------------------------------------------------------------------
-- Controlled perturbation receipt.
------------------------------------------------------------------------

record AvianRFOverlayManipulationReceipt
    (surface : AvianCompassSurface) : Set₁ where
  field
    compassReceipt : PerturbedCompassReceipt surface

    manipulationRole : RFManipulationRole
    injectedFieldGeometry : InjectedFieldGeometry

    controlledPerturbation : PerturbationRegime
    controlledPerturbationMatchesReceipt :
      controlledPerturbation ≡ perturbation compassReceipt

    rfBaseField : MagneticField surface
    rfPerturbedField : MagneticField surface
    rfBaseAngle : FieldAngle surface rfBaseField
    rfPerturbedAngle : FieldAngle surface rfPerturbedField
    rfRadicalPair : RadicalPair surface
    rfSpinState : SpinState surface rfRadicalPair

    baseRetinalYield : RetinalSignal surface
    perturbedRetinalYield : RetinalSignal surface

    fieldAngleChanged :
      angleDistinguishable surface
        rfBaseField
        rfPerturbedField
        rfBaseAngle
        rfPerturbedAngle

    yieldChangedByControlledField :
      yieldDistinguishable surface
        baseRetinalYield
        perturbedRetinalYield

    overlayRewriteStatus : OverlayRewriteStatus
    behaviorReceiptStatus : BehaviorReceiptStatus
    rfOrientationEffect : OrientationEffect

    overlayStatusMatchesEffect :
      overlayRewriteStatus ≡ effectToOverlayRewrite rfOrientationEffect

    behaviorStatusMatchesEffect :
      behaviorReceiptStatus ≡ effectToBehaviorReceiptStatus rfOrientationEffect

    rfNoDirectVisualQualiaReadout : Bool
    rfNoDirectVisualQualiaReadoutIsTrue :
      rfNoDirectVisualQualiaReadout ≡ true

    rfNoEthicalPerturbationLicenseFlag : Bool
    rfNoEthicalPerturbationLicenseFlagIsTrue :
      rfNoEthicalPerturbationLicenseFlag ≡ true

    rfNoCompleteBiophysicsClaim : Bool
    rfNoCompleteBiophysicsClaimIsTrue :
      rfNoCompleteBiophysicsClaim ≡ true

    inverseOverlayProbeObservableOnly : Bool
    inverseOverlayProbeObservableOnlyIsTrue :
      inverseOverlayProbeObservableOnly ≡ true

    manipulationBoundaries : List RFManipulationBoundary
    inverseOverlayProbeReading : String
    controlledManipulationReading : String

open AvianRFOverlayManipulationReceipt public

------------------------------------------------------------------------
-- Canonical wrappers.
------------------------------------------------------------------------

wrapPerturbedCompassReceiptAsRFManipulation :
  {surface : AvianCompassSurface} →
  (role : RFManipulationRole) →
  (geometry : InjectedFieldGeometry) →
  (receipt : PerturbedCompassReceipt surface) →
  AvianRFOverlayManipulationReceipt surface
wrapPerturbedCompassReceiptAsRFManipulation {surface} role geometry receipt =
  record
    { compassReceipt = receipt
    ; manipulationRole = role
    ; injectedFieldGeometry = geometry
    ; controlledPerturbation = perturbation receipt
    ; controlledPerturbationMatchesReceipt = refl
    ; rfBaseField = baseField receipt
    ; rfPerturbedField = perturbedField receipt
    ; rfBaseAngle = baseAngle receipt
    ; rfPerturbedAngle = perturbedAngle receipt
    ; rfRadicalPair = radicalPair receipt
    ; rfSpinState = spinState receipt
    ; baseRetinalYield =
        yield
          surface
          (baseField receipt)
          (baseAngle receipt)
          (radicalPair receipt)
          (spinState receipt)
    ; perturbedRetinalYield =
        yield
          surface
          (perturbedField receipt)
          (perturbedAngle receipt)
          (radicalPair receipt)
          (spinState receipt)
    ; fieldAngleChanged = angleChanged receipt
    ; yieldChangedByControlledField = yieldChanged receipt
    ; overlayRewriteStatus =
        effectToOverlayRewrite (orientationEffect receipt)
    ; behaviorReceiptStatus =
        effectToBehaviorReceiptStatus (orientationEffect receipt)
    ; rfOrientationEffect = orientationEffect receipt
    ; overlayStatusMatchesEffect = refl
    ; behaviorStatusMatchesEffect = refl
    ; rfNoDirectVisualQualiaReadout = true
    ; rfNoDirectVisualQualiaReadoutIsTrue = refl
    ; rfNoEthicalPerturbationLicenseFlag = true
    ; rfNoEthicalPerturbationLicenseFlagIsTrue = refl
    ; rfNoCompleteBiophysicsClaim = true
    ; rfNoCompleteBiophysicsClaimIsTrue = refl
    ; inverseOverlayProbeObservableOnly = true
    ; inverseOverlayProbeObservableOnlyIsTrue = refl
    ; manipulationBoundaries = canonicalRFBoundaries
    ; inverseOverlayProbeReading =
        "Inverse overlay probing is observable-only: RF changes constrain yield, overlay geometry, and behavior without reading visual qualia."
    ; controlledManipulationReading =
        "Controlled RF perturbation is recorded as field change to yield change to orientation effect, not as complete biophysics."
    }

larmorLikeRFManipulationReceipt :
  {surface : AvianCompassSurface} →
  PerturbedCompassReceipt surface →
  AvianRFOverlayManipulationReceipt surface
larmorLikeRFManipulationReceipt =
  wrapPerturbedCompassReceiptAsRFManipulation
    larmorLikeDrive
    transverseInjection

broadbandRFManipulationReceipt :
  {surface : AvianCompassSurface} →
  PerturbedCompassReceipt surface →
  AvianRFOverlayManipulationReceipt surface
broadbandRFManipulationReceipt =
  wrapPerturbedCompassReceiptAsRFManipulation
    broadbandLikeNoise
    rotatingVectorInjection

staticControlManipulationReceipt :
  {surface : AvianCompassSurface} →
  PerturbedCompassReceipt surface →
  AvianRFOverlayManipulationReceipt surface
staticControlManipulationReceipt =
  wrapPerturbedCompassReceiptAsRFManipulation
    staticFieldControl
    shieldedControlGeometry

record RFManipulationNonRecoveryCertificate
    {surface : AvianCompassSurface}
    (receipt : AvianRFOverlayManipulationReceipt surface) : Set where
  field
    qualiaReadoutBlocked :
      rfNoDirectVisualQualiaReadout receipt ≡ true

    ethicsLicenseBlocked :
      rfNoEthicalPerturbationLicenseFlag receipt ≡ true

    completeBiophysicsBlocked :
      rfNoCompleteBiophysicsClaim receipt ≡ true

    inverseProbeObservableOnly :
      inverseOverlayProbeObservableOnly receipt ≡ true

    certificateReading : String

open RFManipulationNonRecoveryCertificate public

canonicalRFManipulationNonRecoveryCertificate :
  {surface : AvianCompassSurface} →
  (receipt : AvianRFOverlayManipulationReceipt surface) →
  RFManipulationNonRecoveryCertificate receipt
canonicalRFManipulationNonRecoveryCertificate receipt =
  record
    { qualiaReadoutBlocked = rfNoDirectVisualQualiaReadoutIsTrue receipt
    ; ethicsLicenseBlocked = rfNoEthicalPerturbationLicenseFlagIsTrue receipt
    ; completeBiophysicsBlocked = rfNoCompleteBiophysicsClaimIsTrue receipt
    ; inverseProbeObservableOnly =
        inverseOverlayProbeObservableOnlyIsTrue receipt
    ; certificateReading =
        "RF overlay manipulation remains an observable-only inverse probe with a non-promotion boundary: it does not license qualia, ethics, or full-mechanism recovery."
    }
