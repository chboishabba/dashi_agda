module DASHI.Biology.AvianCryptochromeMagnetoreceptionInhabitant where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianCompassSurface as Legacy
import DASHI.Biology.MagnetoreceptionSurface as Generic

------------------------------------------------------------------------
-- Adapter: the existing CRY4/radical-pair/retinal lane is retained as one
-- inhabitant of the mechanism-neutral magnetoreception owner.
------------------------------------------------------------------------

record AvianCryptochromeMagnetoreceptionInhabitant : Set₁ where
  field
    legacyCompassSurface :
      Legacy.AvianCompassSurface

    genericSurface :
      Generic.MagnetoreceptionSurface

    genericChannelIsRetinal :
      Generic.channel genericSurface ≡
      Generic.radicalPairRetinalChannel

    genericAfferentRouteIsRetinal :
      Generic.afferentRoute genericSurface ≡
      Generic.retinalNeuralRoute

    cryptochromeMechanismExclusive :
      Bool
    cryptochromeMechanismExclusiveIsFalse :
      cryptochromeMechanismExclusive ≡ false

    visualOverlayUniversal :
      Bool
    visualOverlayUniversalIsFalse :
      visualOverlayUniversal ≡ false

    phenomenalMagneticHUDRecovered :
      Bool
    phenomenalMagneticHUDRecoveredIsFalse :
      phenomenalMagneticHUDRecovered ≡ false

    adapterReading :
      String

open AvianCryptochromeMagnetoreceptionInhabitant public

cryptochromeGenericSurface : Generic.MagnetoreceptionSurface
cryptochromeGenericSurface =
  record
    { MagneticStimulus = Generic.MagnetoToken
    ; ReceptorState = Generic.MagnetoToken
    ; TransductionState = Generic.MagnetoToken
    ; AfferentSignal = Generic.MagnetoToken
    ; NavigationCue = Generic.MagnetoToken
    ; NavigationContext = Generic.MagnetoToken
    ; NavigationPolicy = Generic.MagnetoToken
    ; OrientationOutput = Generic.MagnetoToken
    ; receptorResponse = λ _ _ -> Generic.transductionStateToken
    ; afferentEncode = λ _ -> Generic.afferentSignalToken
    ; cueFromAfference = λ _ _ -> Generic.navigationCueToken
    ; navigationUse = λ _ _ -> Generic.orientationOutputToken
    ; channel = Generic.radicalPairRetinalChannel
    ; afferentRoute = Generic.retinalNeuralRoute
    ; receptorEvidence = Generic.structuralHypothesis
    ; afferentEvidence = Generic.structuralHypothesis
    ; navigationEvidence = Generic.perturbationReceipt
    ; boundaries = Generic.canonicalMechanismNeutralBoundaries
    ; surfaceReading =
        "CRY4/radical-pair/retinal mechanism represented as one non-exclusive magnetoreception inhabitant."
    }

canonicalAvianCryptochromeMagnetoreceptionInhabitant :
  (legacy : Legacy.AvianCompassSurface) ->
  AvianCryptochromeMagnetoreceptionInhabitant
canonicalAvianCryptochromeMagnetoreceptionInhabitant legacy =
  record
    { legacyCompassSurface = legacy
    ; genericSurface = cryptochromeGenericSurface
    ; genericChannelIsRetinal = refl
    ; genericAfferentRouteIsRetinal = refl
    ; cryptochromeMechanismExclusive = false
    ; cryptochromeMechanismExclusiveIsFalse = refl
    ; visualOverlayUniversal = false
    ; visualOverlayUniversalIsFalse = refl
    ; phenomenalMagneticHUDRecovered = false
    ; phenomenalMagneticHUDRecoveredIsFalse = refl
    ; adapterReading =
        "The old retinal chain is preserved but demoted from canonical avian compass ontology to one evidence-bounded inhabitant."
    }
