module DASHI.Physics.Motors.DriverIndependentSourcePortBidiExact where

-- Finite structural BIDI. A ZVS implementation is not the canonical device.
-- Claim identity: original source-specific network + physical external ports.

open import Agda.Builtin.Equality using (_≡_; refl)

data DriverTechnology : Set where
  zvs : DriverTechnology
  flyback : DriverTechnology
  neonTransformer : DriverTechnology
  unspecifiedDrivenResonator : DriverTechnology

data EnergyPort : Set where
  drivenSupply : EnergyPort
  earthElectrode : EnergyPort
  atmosphericField : EnergyPort
  incidentRF : EnergyPort
  ionisingParticles : EnergyPort
  usefulOutput : EnergyPort
  internalLoss : EnergyPort
  storageChange : EnergyPort

data Configuration : Set where
  smithLoadedDipole : Configuration
  smithSuitcaseTen : Configuration
  smithSuitcaseEleven : Configuration
  filsingerEarth : Configuration
  filsingerPortableProposal : Configuration

record CandidateNetwork : Set where
  constructor candidateNetwork
  field
    sourceConfiguration : Configuration
    driverImplementation : DriverTechnology
    externalPort : EnergyPort

replaceDriver : DriverTechnology → CandidateNetwork → CandidateNetwork
replaceDriver d (candidateNetwork c old p) = candidateNetwork c d p

sourceConfigurationPreserved :
  (d : DriverTechnology) (n : CandidateNetwork) →
  CandidateNetwork.sourceConfiguration (replaceDriver d n) ≡
  CandidateNetwork.sourceConfiguration n
sourceConfigurationPreserved d (candidateNetwork c old p) = refl

externalPortPreserved :
  (d : DriverTechnology) (n : CandidateNetwork) →
  CandidateNetwork.externalPort (replaceDriver d n) ≡
  CandidateNetwork.externalPort n
externalPortPreserved d (candidateNetwork c old p) = refl

-- Not a physical equivalence: Earth-to-antenna changes port identity.
portableCandidate : CandidateNetwork → CandidateNetwork
portableCandidate (candidateNetwork c d p) =
  candidateNetwork filsingerPortableProposal d incidentRF

data Contradiction : Set where

earthPortNotRF : earthElectrode ≡ incidentRF → Contradiction
earthPortNotRF ()

-- Reverse admission must come from a measured same-object circuit.
record SameDeviceEnergyAdmission (n : CandidateNetwork) : Set₁ where
  field
    SelectedPhysicalNetlist : Set
    CalibratedDrivingRealPower : Set
    CalibratedExternalRealPower : Set
    CalibratedStorageAndLosses : Set
    physicalNetlist : SelectedPhysicalNetlist
    inputReceipt : CalibratedDrivingRealPower
    externalReceipt : CalibratedExternalRealPower
    ledgerReceipt : CalibratedStorageAndLosses
