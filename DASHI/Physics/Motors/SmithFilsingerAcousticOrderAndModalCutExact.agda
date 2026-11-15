module DASHI.Physics.Motors.SmithFilsingerAcousticOrderAndModalCutExact where

-- Original 2026-11-15 acoustic-source timing/finite energy contracts.
-- These source-indexed acoustic events are NOT actual switch pin times.
-- No acoustic response is automatically a distinct physical component.
-- Work in Nat energy quanta, reusing Circuit36927 bounds.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Energy
import DASHI.Physics.Motors.SmithFilsingerPumpOffDualPathExact as Pump

-- Integer milliseconds relative to the 60 second recording anchor;
-- markers are rounded values from a source-original 2048-point STFT replay.
firstUpperAcousticPeakMs : Nat
firstUpperAcousticPeakMs = 405

carrierHalfAmplitudeFallMs : Nat
carrierHalfAmplitudeFallMs = 532

secondUpperAcousticPeakMs : Nat
secondUpperAcousticPeakMs = 715

firstAcousticPeakBeforeAudibleFall :
  Energy._≤_ firstUpperAcousticPeakMs carrierHalfAmplitudeFallMs
firstAcousticPeakBeforeAudibleFall = Energy.≤-append 405 127

audibleFallBeforeSecondAcousticPeak :
  Energy._≤_ carrierHalfAmplitudeFallMs secondUpperAcousticPeakMs
audibleFallBeforeSecondAcousticPeak = Energy.≤-append 532 183

firstAcousticPeakBeforeSecond :
  Energy._≤_ firstUpperAcousticPeakMs secondUpperAcousticPeakMs
firstAcousticPeakBeforeSecond = Energy.≤-append 405 310

data Empty : Set where

data ClockKind : Set where
  audioPeak audioCarrierFall measuredElectricalSwitch : ClockKind

acousticPeakNotElectricalSwitch :
  audioPeak ≡ measuredElectricalSwitch → Empty
acousticPeakNotElectricalSwitch ()

data Mode : Set where
  broadbandResponse narrowbandResponse : Mode

data Component : Set where
  multiModalNetwork : Component

-- A single physical member or network may carry two unequal modes.
modeOwner : Mode → Component
modeOwner broadbandResponse = multiModalNetwork
modeOwner narrowbandResponse = multiModalNetwork

modesDifferent : broadbandResponse ≡ narrowbandResponse → Empty
modesDifferent ()

sameComponentCanCarryBothModes :
  modeOwner broadbandResponse ≡ modeOwner narrowbandResponse
sameComponentCanCarryBothModes = refl

AllDifferentModesHaveDifferentComponents : Set
AllDifferentModesHaveDifferentComponents =
  (m n : Mode) → (m ≡ n → Empty) →
  (modeOwner m ≡ modeOwner n → Empty)

observedModesAloneDoNotIdentifyDifferentComponents :
  AllDifferentModesHaveDifferentComponents → Empty
observedModesAloneDoNotIdentifyDifferentComponents separates =
  separates broadbandResponse narrowbandResponse modesDifferent refl

record FinitePassiveModalLedger : Set where
  constructor finitePassiveModalLedger
  field
    initialAllModeEnergy finalAllModeEnergy lostOrExportedEnergy : Nat
    passiveBoundary :
      initialAllModeEnergy ≡ finalAllModeEnergy + lostOrExportedEnergy

passiveAllModesCannotGainStoredEnergy : (r : FinitePassiveModalLedger) →
  Energy._≤_ (FinitePassiveModalLedger.finalAllModeEnergy r)
             (FinitePassiveModalLedger.initialAllModeEnergy r)
passiveAllModesCannotGainStoredEnergy r =
  Energy.transportUpper
    (Energy.sym (FinitePassiveModalLedger.passiveBoundary r))
    (Energy.≤-append (FinitePassiveModalLedger.finalAllModeEnergy r)
                     (FinitePassiveModalLedger.lostOrExportedEnergy r))

-- A different internal mode can rise while total energy falls:
-- initial 10 quanta, 7 final in all modes, 3 lost/exported.
passiveExample : FinitePassiveModalLedger
passiveExample = finitePassiveModalLedger 10 7 3 refl

lateInternalModeCanRiseWithoutExternalInput : Energy._≤_ 0 4
lateInternalModeCanRiseWithoutExternalInput = Energy.≤-append 0 4

passiveExampleFinalBound :
  Energy._≤_ (FinitePassiveModalLedger.finalAllModeEnergy passiveExample)
             (FinitePassiveModalLedger.initialAllModeEnergy passiveExample)
passiveExampleFinalBound = passiveAllModesCannotGainStoredEnergy passiveExample

record SamePhysicalClockAndModeAdmission : Set₁ where
  field
    ActualSwitchOffClock : Set
    SameComponentElectricalEigenmodes : Set
    CalibratedElectromechanicalObservation : Set
    SignedDriveNaturalAndLossWork : Set
    switchClock : ActualSwitchOffClock
    electricalModes : SameComponentElectricalEigenmodes
    observation : CalibratedElectromechanicalObservation
    energyReceipt : SignedDriveNaturalAndLossWork

-- No constructor of SamePhysicalClockAndModeAdmission is furnished.
