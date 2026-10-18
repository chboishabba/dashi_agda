module DASHI.Biology.AvianMagneticFieldPerturbationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.MagnetoreceptionSurface as Generic

------------------------------------------------------------------------
-- Mechanism-neutral magnetic perturbation owner.
--
-- A controlled field manipulation constrains the stimulus presented to a
-- magnetoreception surface and the resulting behavioral receipt.  It does not
-- identify whether the biological receptor is retinal/radical-pair, hepatic
-- macrophage, vestibular, trigeminal, or another mechanism.
------------------------------------------------------------------------

data FieldPerturbationMode : Set where
  baselineGeomagneticField : FieldPerturbationMode
  staticFieldRotation : FieldPerturbationMode
  staticFieldIntensityShift : FieldPerturbationMode
  oscillatingRFField : FieldPerturbationMode
  broadbandRFNoise : FieldPerturbationMode
  pulsedFieldProbe : FieldPerturbationMode
  shamFieldControl : FieldPerturbationMode

data FieldGeometryClass : Set where
  collinearGeometry : FieldGeometryClass
  transverseGeometry : FieldGeometryClass
  obliqueGeometry : FieldGeometryClass
  rotatingVectorGeometry : FieldGeometryClass
  spatialGradientGeometry : FieldGeometryClass
  shieldedControlGeometry : FieldGeometryClass

data BehavioralPerturbationEffect : Set where
  stableOrientation : BehavioralPerturbationEffect
  shiftedOrientation : BehavioralPerturbationEffect
  randomizedOrientation : BehavioralPerturbationEffect
  degradedOrientationConfidence : BehavioralPerturbationEffect
  refusalOrientation : BehavioralPerturbationEffect
  invertedOrientation : BehavioralPerturbationEffect

data PerturbationBoundary : Set where
  noPerturbationToReceptorIdentityClaim : PerturbationBoundary
  noRFDisruptionToQuantumMechanismProof : PerturbationBoundary
  noStaticRotationToIronMechanismProof : PerturbationBoundary
  noBehaviorToNeuralCodeRecovery : PerturbationBoundary
  noBehaviorToPhenomenologyRecovery : PerturbationBoundary
  noApparatusGeometryToBiologicalMechanismIdentity : PerturbationBoundary

record AvianMagneticFieldPerturbationReceipt
    (surface : Generic.MagnetoreceptionSurface) : Set₁ where
  field
    BaseStimulus :
      Generic.MagneticStimulus surface

    PerturbedStimulus :
      Generic.MagneticStimulus surface

    ReceptorContext :
      Generic.ReceptorState surface

    NavigationContext :
      Generic.NavigationContext surface

    NavigationPolicy :
      Generic.NavigationPolicy surface

    mode :
      FieldPerturbationMode

    geometry :
      FieldGeometryClass

    baseTransduction :
      Generic.TransductionState surface

    perturbedTransduction :
      Generic.TransductionState surface

    baseTransductionMatches :
      baseTransduction ≡
      Generic.receptorResponse surface BaseStimulus ReceptorContext

    perturbedTransductionMatches :
      perturbedTransduction ≡
      Generic.receptorResponse surface PerturbedStimulus ReceptorContext

    baseAfference :
      Generic.AfferentSignal surface

    perturbedAfference :
      Generic.AfferentSignal surface

    baseAfferenceMatches :
      baseAfference ≡ Generic.afferentEncode surface baseTransduction

    perturbedAfferenceMatches :
      perturbedAfference ≡ Generic.afferentEncode surface perturbedTransduction

    behavioralEffect :
      BehavioralPerturbationEffect

    perturbationObserved :
      Bool

    perturbationObservedIsTrue :
      perturbationObserved ≡ true

    receptorMechanismIdentifiedByPerturbation :
      Bool

    receptorMechanismIdentifiedByPerturbationIsFalse :
      receptorMechanismIdentifiedByPerturbation ≡ false

    neuralCodeRecovered :
      Bool

    neuralCodeRecoveredIsFalse :
      neuralCodeRecovered ≡ false

    phenomenalContentRecovered :
      Bool

    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    boundaries :
      List PerturbationBoundary

    receiptReading :
      String

open AvianMagneticFieldPerturbationReceipt public

canonicalPerturbationBoundaries : List PerturbationBoundary
canonicalPerturbationBoundaries =
  noPerturbationToReceptorIdentityClaim
  ∷ noRFDisruptionToQuantumMechanismProof
  ∷ noStaticRotationToIronMechanismProof
  ∷ noBehaviorToNeuralCodeRecovery
  ∷ noBehaviorToPhenomenologyRecovery
  ∷ noApparatusGeometryToBiologicalMechanismIdentity
  ∷ []

canonicalMechanismNeutralPerturbationReceipt :
  AvianMagneticFieldPerturbationReceipt
    Generic.canonicalMechanismNeutralMagnetoreceptionSurface
canonicalMechanismNeutralPerturbationReceipt =
  record
    { BaseStimulus = Generic.magneticStimulusToken
    ; PerturbedStimulus = Generic.magneticStimulusToken
    ; ReceptorContext = Generic.receptorStateToken
    ; NavigationContext = Generic.navigationContextToken
    ; NavigationPolicy = Generic.navigationPolicyToken
    ; mode = oscillatingRFField
    ; geometry = transverseGeometry
    ; baseTransduction = Generic.transductionStateToken
    ; perturbedTransduction = Generic.transductionStateToken
    ; baseTransductionMatches = refl
    ; perturbedTransductionMatches = refl
    ; baseAfference = Generic.afferentSignalToken
    ; perturbedAfference = Generic.afferentSignalToken
    ; baseAfferenceMatches = refl
    ; perturbedAfferenceMatches = refl
    ; behavioralEffect = degradedOrientationConfidence
    ; perturbationObserved = true
    ; perturbationObservedIsTrue = refl
    ; receptorMechanismIdentifiedByPerturbation = false
    ; receptorMechanismIdentifiedByPerturbationIsFalse = refl
    ; neuralCodeRecovered = false
    ; neuralCodeRecoveredIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; boundaries = canonicalPerturbationBoundaries
    ; receiptReading =
        "Controlled magnetic perturbation constrains stimulus and behavioral response while receptor identity, neural code, and phenomenal content remain unpromoted."
    }
