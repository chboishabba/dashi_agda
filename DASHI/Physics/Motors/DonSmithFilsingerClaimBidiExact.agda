module DASHI.Physics.Motors.DonSmithFilsingerClaimBidiExact where

-- Source-qualified claim/obligation BIDI; finite non-identifiability proof.
-- Historical owner: Donald Lee Smith MXNL02000035A, application published 2004.
-- Modern owner: speaker Filsinger's Earth-ZVS and proposed portable reels.
-- This is NOT a Maxwell PDE eigenmode solver or excess-energy certificate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

data Contradiction : Set where

data Device : Set where
  smithApplicationDevice : Device
  filsingerEarthZVS : Device
  filsingerPortableProposal : Device

data OriginalClaim : Set where
  smithLoadedDipoleResonance : OriginalClaim
  filsingerZVSSwitching : OriginalClaim
  filsingerMegohmLoading : OriginalClaim
  filsingerEarthContribution : OriginalClaim
  filsingerPortableMidpointPlate : OriginalClaim
  filsingerCosmicRadiation : OriginalClaim

claimOwner : OriginalClaim → Device
claimOwner smithLoadedDipoleResonance = smithApplicationDevice
claimOwner filsingerZVSSwitching = filsingerEarthZVS
claimOwner filsingerMegohmLoading = filsingerEarthZVS
claimOwner filsingerEarthContribution = filsingerEarthZVS
claimOwner filsingerPortableMidpointPlate = filsingerPortableProposal
claimOwner filsingerCosmicRadiation = filsingerPortableProposal

-- Forward: what an original speaker's proposed model would make
-- observable IF its mechanisms and antecedents were realised.
data ObservableGate : Set where
  coilOrDipoleResponse : ObservableGate
  electricalClock : ObservableGate
  differentialShuntPower : ObservableGate
  signedGroundWork : ObservableGate
  measuredPlateCurrentMode : ObservableGate
  independentlyDepositedRadiationWork : ObservableGate

prediction : OriginalClaim → ObservableGate
prediction smithLoadedDipoleResonance = coilOrDipoleResponse
prediction filsingerZVSSwitching = electricalClock
prediction filsingerMegohmLoading = differentialShuntPower
prediction filsingerEarthContribution = signedGroundWork
prediction filsingerPortableMidpointPlate = measuredPlateCurrentMode
prediction filsingerCosmicRadiation = independentlyDepositedRadiationWork

-- Reverse: no observation can be elevated to a physical cause without
-- a selected same-object source/calibration and full port energy budget.
record ReversePhysicalObligations (claim : OriginalClaim) : Set₁ where
  field
    SelectedSameDevice : Set
    ActualFieldAndPortMeasurements : Set
    SourceSeparationAndLosses : Set
    selectedDevice : SelectedSameDevice
    portMeasurements : ActualFieldAndPortMeasurements
    allSourcesAndLosses : SourceSeparationAndLosses

-- Reuse actual canonical circuit and Maxwell source owners rather
-- than manufacture a second universal circuit or Maxwell object.
record ExistingOwnerReuse : Set where
  field
    candidatePin : Circuit.Pin
    symbolicCurvature : Maxwell.TwoForm

-- Distinct physical operating circuits cannot be identified merely
-- because the same source narrator discusses both.
earthAndPortableDistinct :
  filsingerEarthZVS ≡ filsingerPortableProposal → Contradiction
earthAndPortableDistinct ()

-- Two finite worlds exhibit identical apparent meter indications
-- despite different environmental contribution classifications.
data EnvironmentWorld : Set where
  noMeasuredEnvironmentalContribution : EnvironmentWorld
  independentlyMeasuredEnvironmentalContribution : EnvironmentWorld

data MeterResult : Set where
  sameVoltageDisplay : MeterResult

meter : EnvironmentWorld → MeterResult
meter noMeasuredEnvironmentalContribution = sameVoltageDisplay
meter independentlyMeasuredEnvironmentalContribution = sameVoltageDisplay

data EnvironmentalClassification : Set where
  zeroContribution : EnvironmentalClassification
  nonzeroContribution : EnvironmentalClassification

environmentalClass : EnvironmentWorld → EnvironmentalClassification
environmentalClass noMeasuredEnvironmentalContribution = zeroContribution
environmentalClass independentlyMeasuredEnvironmentalContribution = nonzeroContribution

classDistinct : zeroContribution ≡ nonzeroContribution → Contradiction
classDistinct ()

MeterIdentifiesEnvironmentalContribution : Set
MeterIdentifiesEnvironmentalContribution =
  (x y : EnvironmentWorld) →
  meter x ≡ meter y → environmentalClass x ≡ environmentalClass y

meterDoesNotIdentifyEnvironmentalPower :
  MeterIdentifiesEnvironmentalContribution → Contradiction
meterDoesNotIdentifyEnvironmentalPower identifies =
  classDistinct
    (identifies noMeasuredEnvironmentalContribution
      independentlyMeasuredEnvironmentalContribution refl)

-- Source documents and witness measurements are independent:
-- no witness of ReversePhysicalObligations is constructed.
