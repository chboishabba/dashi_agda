module DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact where

-- Original DASHI source-qualified contribution (2026-11-15).
-- Finite discrete causality and accounting contracts; NOT same-device
-- Maxwell/plasma proof or observed environmental power.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Circuit
import DASHI.Physics.Motors.Circuit36927SwitchStateExact as Switch
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell
import DASHI.Physics.Motors.DonSmithFilsingerClaimBidiExact as SmithBidi

data SourceFamily : Set where
  smithCompiled kellyDarrer filsingerEarth filsingerPortable ourSpecifiedModel : SourceFamily

data PhysicalMember : Set where
  pumpDriver hvStorage switchDump transformer splitSecondary : PhysicalMember
  rectifier earthElectrode goldenPlate ionosphereMode : PhysicalMember

data WaveChannel : Set where
  fastCarrier slowEnvelope convertedELF transmittedHF : WaveChannel
  reflectedElectrical outgoingMaxwell : WaveChannel

record MemberState : Set where
  constructor memberState
  field
    member : PhysicalMember
    timeIndex : Nat
    componentPin : Circuit.Endpoint
    switchState : Switch.SwitchState
    symbolicField : Maxwell.TwoForm
    carrier : WaveChannel
    sourceOwner : SourceFamily

-- Explicit launch, flight and arrival distinguish retarded coupling
-- from a fictitious instantaneous global circuit voltage.
record RetardedFlight : Set where
  constructor retardedFlight
  field
    launch flight arrival : Nat
    travelLaw : launch + flight ≡ arrival

scheduled : (start duration : Nat) → RetardedFlight
scheduled start duration =
  retardedFlight start duration (start + duration) refl

arrivalNoEarlier : (f : RetardedFlight) →
  Bound._≤_ (RetardedFlight.launch f) (RetardedFlight.arrival f)
arrivalNoEarlier f =
  Bound.transportUpper
    (RetardedFlight.travelLaw f)
    (Bound.≤-append (RetardedFlight.launch f)
                    (RetardedFlight.flight f))

sucCong : ∀ {a b : Nat} → a ≡ b → suc a ≡ suc b
sucCong refl = refl

postpone : RetardedFlight → RetardedFlight
postpone (retardedFlight t d a law) =
  retardedFlight (suc t) d (suc a) (sucCong law)

postponePreservesFlight : (f : RetardedFlight) →
  RetardedFlight.flight (postpone f) ≡ RetardedFlight.flight f
postponePreservesFlight (retardedFlight t d a law) = refl

twoHopSecondFlight : (start firstDelay secondDelay : Nat) → RetardedFlight
twoHopSecondFlight start firstDelay secondDelay =
  scheduled (start + firstDelay) secondDelay

-- Signed real work in a finite interval is represented by distinct
-- nonnegative source-input and loss-output energy grids.
record BoundedWorkWindow : Set where
  constructor boundedWorkWindow
  field
    startTime endTime : Nat
    driverInput naturalSourceInput modulatorInput initialStored : Nat
    usefulOutput dissipated reradiated finalStored : Nat
    completeBoundaryBalance :
      ((driverInput + naturalSourceInput) + modulatorInput) + initialStored
      ≡ usefulOutput + (dissipated + (reradiated + finalStored))

allAvailable : BoundedWorkWindow → Nat
allAvailable r =
  ((BoundedWorkWindow.driverInput r + BoundedWorkWindow.naturalSourceInput r)
      + BoundedWorkWindow.modulatorInput r) + BoundedWorkWindow.initialStored r

usefulNoGreaterThanAllSources : (r : BoundedWorkWindow) →
  Bound._≤_ (BoundedWorkWindow.usefulOutput r) (allAvailable r)
usefulNoGreaterThanAllSources r =
  Bound.transportUpper
    (Bound.sym (BoundedWorkWindow.completeBoundaryBalance r))
    (Bound.≤-append (BoundedWorkWindow.usefulOutput r)
      (BoundedWorkWindow.dissipated r
       + (BoundedWorkWindow.reradiated r + BoundedWorkWindow.finalStored r)))

-- Acoustic-only observation cannot identify environmental work:
-- two model worlds have exactly the same acoustic label.
data Empty : Set where

data ElectricalWorld : Set where
  drivenOnly naturalSourceAlsoCoupled : ElectricalWorld

data AcousticObservation : Set where
  sameSevenEightKilohertzTone : AcousticObservation

acoustic : ElectricalWorld → AcousticObservation
acoustic drivenOnly = sameSevenEightKilohertzTone
acoustic naturalSourceAlsoCoupled = sameSevenEightKilohertzTone

data NaturalInputClass : Set where
  absent present : NaturalInputClass

naturalInputClass : ElectricalWorld → NaturalInputClass
naturalInputClass drivenOnly = absent
naturalInputClass naturalSourceAlsoCoupled = present

absentNotPresent : absent ≡ present → Empty
absentNotPresent ()

AudioIdentifiesNaturalSource : Set
AudioIdentifiesNaturalSource =
  (x y : ElectricalWorld) →
  acoustic x ≡ acoustic y → naturalInputClass x ≡ naturalInputClass y

acousticAloneCannotIdentifyNaturalSource :
  AudioIdentifiesNaturalSource → Empty
acousticAloneCannotIdentifyNaturalSource identifies =
  absentNotPresent (identifies drivenOnly naturalSourceAlsoCoupled refl)

-- Uninhabited reverse physical admission, never forged from spectra.
record SameObjectPhysicalWeld : Set₁ where
  field
    SelectedReelAndSmithSource : Set
    ActualWellFormedPinLevelNetlist : Set
    SpecifiedConstitutiveNonlinearities : Set
    CausalSpatialMaxwellSolution : Set
    TimeSynchronousElectricalAndAcousticTrace : Set
    CalibratedNaturalDriverAndPumpWork : Set
    sourceReadback : SelectedReelAndSmithSource
    pinReadback : ActualWellFormedPinLevelNetlist
    materialReadback : SpecifiedConstitutiveNonlinearities
    spatialField : CausalSpatialMaxwellSolution
    traceReceipt : TimeSynchronousElectricalAndAcousticTrace
    energyReceipt : CalibratedNaturalDriverAndPumpWork
