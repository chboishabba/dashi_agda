module DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact where

-- Source-faithful forward/reverse obligations for a coupled receiver.
-- Reflection here is an explicit uninhabited PHYSICAL receipt, not a
-- numerical proof that the historical apparatus harvests ambient power.
-- Canonical port identities remain driver-independent.
open import Agda.Builtin.Equality using (_≡_; refl)

data Contradiction : Set where

data PortKind : Set where
  poweredDriver earthElectrode atmosphere ambientRF ionisingParticles : PortKind
  usefulLoad internalLoss reactiveStorage : PortKind

data ReflectionKind : Set where
  mutualImpedanceReflectedToDrive : ReflectionKind
  EMWaveReradiatedToExternalPort : ReflectionKind
  outputCouplingIntoUsefulLoad : ReflectionKind

mutualReflectionNotRadiation :
  mutualImpedanceReflectedToDrive ≡ EMWaveReradiatedToExternalPort →
  Contradiction
mutualReflectionNotRadiation ()

data Configuration : Set where
  smithSuitcaseFigureTen : Configuration
  filsingerEarthNarration : Configuration
  filsingerPortableProposal : Configuration

record CandidateCoupling : Set where
  constructor selectedCoupling
  field
    sourceCircuit : Configuration
    driverPort : PortKind
    environmentalPort : PortKind

-- Conceptually changing the power converter cannot silently create
-- another source port.
replaceDriverPort : PortKind → CandidateCoupling → CandidateCoupling
replaceDriverPort new (selectedCoupling c old env) =
  selectedCoupling c new env

environmentUnchangedByDriverReplacement :
  (p : PortKind) (c : CandidateCoupling) →
  CandidateCoupling.environmentalPort (replaceDriverPort p c) ≡
  CandidateCoupling.environmentalPort c
environmentUnchangedByDriverReplacement p (selectedCoupling c old env) = refl

-- The narrated Earth circuit and portable proposal differ in their
-- original-source identification, and are not asserted equivalent.
earthNotPortable :
  filsingerEarthNarration ≡ filsingerPortableProposal → Contradiction
earthNotPortable ()

record MeasuredReciprocalReflection : Set₁ where
  field
    SelectedPhysicalBoundaryAndFeed : Set
    MeasuredComplexIncidentWave : Set
    MeasuredComplexOutgoingWave : Set
    MeasuredDriverReflectedLoad : Set
    MaxwellAndCircuitPortAgreement : Set
    physicalBoundary : SelectedPhysicalBoundaryAndFeed
    incident : MeasuredComplexIncidentWave
    outgoing : MeasuredComplexOutgoingWave
    reflectedImpedance : MeasuredDriverReflectedLoad
    commonPortReceipt : MaxwellAndCircuitPortAgreement

record EnvironmentalRealPowerClosure : Set₁ where
  field
    ActualSourceIdentity : Set
    SignedSourcePortPower : Set
    CalibratedUsefulOutputPower : Set
    CalibratedDriveAndAllStorageLoss : Set
    physicalSource : ActualSourceIdentity
    signedExternalWork : SignedSourcePortPower
    usefulOutput : CalibratedUsefulOutputPower
    completeEnergyBudget : CalibratedDriveAndAllStorageLoss

-- Nothing above inhabits either physical receipt. The Maxwell
-- golden rectangle and nonlinear coefficient weld remain OPEN.
