module DASHI.Biology.AvianRFOverlayMechanismAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianCompassExamples as LegacyExamples
import DASHI.Biology.AvianRFOverlayManipulationReceipt as LegacyRF
import DASHI.Biology.AvianCryptochromeMagnetoreceptionInhabitant as Cry
import DASHI.Biology.AvianMagneticFieldPerturbationReceipt as GenericRF
import DASHI.Biology.MagnetoreceptionSurface as Generic

------------------------------------------------------------------------
-- The old RF/retinal overlay formalization remains valid as a
-- cryptochrome/radical-pair-specific inhabitant of the new generic magnetic
-- perturbation surface.  The adapter prevents old CRY-specific fields from
-- being mistaken for mechanism-neutral experimental evidence.
------------------------------------------------------------------------

record AvianRFOverlayMechanismAdapter : Set₁ where
  field
    legacyRFReceipt :
      LegacyRF.AvianRFOverlayManipulationReceipt
        LegacyExamples.canonicalAvianCompassSurface

    cryptochromeInhabitant :
      Cry.AvianCryptochromeMagnetoreceptionInhabitant

    genericPerturbation :
      GenericRF.AvianMagneticFieldPerturbationReceipt
        Cry.cryptochromeGenericSurface

    legacyRouteIsCryptochromeSpecific :
      Bool

    legacyRouteIsCryptochromeSpecificIsTrue :
      legacyRouteIsCryptochromeSpecific ≡ true

    legacyRouteIsMechanismNeutral :
      Bool

    legacyRouteIsMechanismNeutralIsFalse :
      legacyRouteIsMechanismNeutral ≡ false

    genericRFDisruptionProvesRadicalPairMechanism :
      Bool

    genericRFDisruptionProvesRadicalPairMechanismIsFalse :
      genericRFDisruptionProvesRadicalPairMechanism ≡ false

    adapterReading :
      String

open AvianRFOverlayMechanismAdapter public

canonicalLegacyRFReceipt :
  LegacyRF.AvianRFOverlayManipulationReceipt
    LegacyExamples.canonicalAvianCompassSurface
canonicalLegacyRFReceipt =
  LegacyRF.broadbandRFManipulationReceipt
    LegacyExamples.rfPerturbationReceipt

canonicalCryptochromePerturbationReceipt :
  GenericRF.AvianMagneticFieldPerturbationReceipt
    Cry.cryptochromeGenericSurface
canonicalCryptochromePerturbationReceipt =
  record
    { BaseStimulus = Generic.magneticStimulusToken
    ; PerturbedStimulus = Generic.magneticStimulusToken
    ; ReceptorContext = Generic.receptorStateToken
    ; NavigationContext = Generic.navigationContextToken
    ; NavigationPolicy = Generic.navigationPolicyToken
    ; mode = GenericRF.oscillatingRFField
    ; geometry = GenericRF.rotatingVectorGeometry
    ; baseTransduction = Generic.transductionStateToken
    ; perturbedTransduction = Generic.transductionStateToken
    ; baseTransductionMatches = refl
    ; perturbedTransductionMatches = refl
    ; baseAfference = Generic.afferentSignalToken
    ; perturbedAfference = Generic.afferentSignalToken
    ; baseAfferenceMatches = refl
    ; perturbedAfferenceMatches = refl
    ; behavioralEffect = GenericRF.degradedOrientationConfidence
    ; perturbationObserved = true
    ; perturbationObservedIsTrue = refl
    ; receptorMechanismIdentifiedByPerturbation = false
    ; receptorMechanismIdentifiedByPerturbationIsFalse = refl
    ; neuralCodeRecovered = false
    ; neuralCodeRecoveredIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; boundaries = GenericRF.canonicalPerturbationBoundaries
    ; receiptReading =
        "Legacy CRY4/radical-pair RF overlay path adapted into the generic perturbation grammar without promoting RF disruption to receptor-mechanism proof."
    }

canonicalAvianRFOverlayMechanismAdapter :
  AvianRFOverlayMechanismAdapter
canonicalAvianRFOverlayMechanismAdapter =
  record
    { legacyRFReceipt = canonicalLegacyRFReceipt
    ; cryptochromeInhabitant =
        Cry.canonicalAvianCryptochromeMagnetoreceptionInhabitant
          LegacyExamples.canonicalAvianCompassSurface
    ; genericPerturbation =
        canonicalCryptochromePerturbationReceipt
    ; legacyRouteIsCryptochromeSpecific = true
    ; legacyRouteIsCryptochromeSpecificIsTrue = refl
    ; legacyRouteIsMechanismNeutral = false
    ; legacyRouteIsMechanismNeutralIsFalse = refl
    ; genericRFDisruptionProvesRadicalPairMechanism = false
    ; genericRFDisruptionProvesRadicalPairMechanismIsFalse = refl
    ; adapterReading =
        "Existing AvianRFOverlayManipulationReceipt is preserved as the CRY-specific branch under the new mechanism-neutral perturbation owner."
    }
