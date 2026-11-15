module DASHI.Physics.Motors.SmithFilsingerPumpOffDualPathExact where

-- Original conditional finite source-port and two-return-path contracts.
-- Acoustic fitting does not establish actual Earth/ionosphere propagation.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.SmithFilsingerHybridRegimeStudyBidiExact as Hybrid

record IsolatedPumpOffLedger : Set where
  constructor isolatedPumpOffLedger
  field
    initialStored usefulOutput heatAndRadiation finalStored : Nat
    sourceBoundaryBalance :
      initialStored ≡ usefulOutput + (heatAndRadiation + finalStored)

-- Conditional theorem: no unmodelled source input after pump-off.
postPumpUsefulBound :
  (r : IsolatedPumpOffLedger) →
  Bound._≤_ (IsolatedPumpOffLedger.usefulOutput r)
            (IsolatedPumpOffLedger.initialStored r)
postPumpUsefulBound r =
  Bound.transportUpper
    (Bound.sym (IsolatedPumpOffLedger.sourceBoundaryBalance r))
    (Bound.≤-append (IsolatedPumpOffLedger.usefulOutput r)
       (IsolatedPumpOffLedger.heatAndRadiation r
        + IsolatedPumpOffLedger.finalStored r))

firstRetardedPath : Nat → Nat → Time.RetardedFlight
firstRetardedPath launch delay = Time.scheduled launch delay

secondRetardedPath : Nat → Nat → Time.RetardedFlight
secondRetardedPath launch delay = Time.scheduled launch delay

sameInitialEventForTwoPaths : (t d1 d2 : Nat) →
  Time.RetardedFlight.launch (firstRetardedPath t d1) ≡
  Time.RetardedFlight.launch (secondRetardedPath t d2)
sameInitialEventForTwoPaths t d1 d2 = refl

firstPathCannotArriveBeforeSource : (t d : Nat) →
  Bound._≤_ t (Time.RetardedFlight.arrival (firstRetardedPath t d))
firstPathCannotArriveBeforeSource t d =
  Time.arrivalNoEarlier (firstRetardedPath t d)

secondPathCannotArriveBeforeSource : (t d : Nat) →
  Bound._≤_ t (Time.RetardedFlight.arrival (secondRetardedPath t d))
secondPathCannotArriveBeforeSource t d =
  Time.arrivalNoEarlier (secondRetardedPath t d)

-- Two mechanisms can have identical two-peak acoustic observations.
data AcousticCause : Set where
  oneSwitchTwoPaths separateAcousticEvents : AcousticCause

data RecordedTwoPeakSignature : Set where
  twoPeaksAfterPumpOff : RecordedTwoPeakSignature

observedPeakSignature : AcousticCause → RecordedTwoPeakSignature
observedPeakSignature oneSwitchTwoPaths = twoPeaksAfterPumpOff
observedPeakSignature separateAcousticEvents = twoPeaksAfterPumpOff

data Empty : Set where

causeNotEqual : oneSwitchTwoPaths ≡ separateAcousticEvents → Empty
causeNotEqual ()

AcousticPeakIdentifiesCause : Set
AcousticPeakIdentifiesCause =
  (a b : AcousticCause) →
  observedPeakSignature a ≡ observedPeakSignature b → a ≡ b

acousticTwoPeakAloneDoesNotIdentifyCause : AcousticPeakIdentifiesCause → Empty
acousticTwoPeakAloneDoesNotIdentifyCause inverse =
  causeNotEqual (inverse oneSwitchTwoPaths separateAcousticEvents refl)

pumpOffIsNotDrivenHunting :
  Hybrid.next Hybrid.switchOff Hybrid.drivenHunting ≡ Hybrid.drivenHunting → Empty
pumpOffIsNotDrivenHunting ()

record SameCircuitPumpOffPhysicalAdmission : Set₁ where
  field
    SelectedOriginalPins : Set
    ActualSwitchOffEventTime : Set
    CoherentElectricalModes : Set
    MechanicalTransferFunction : Set
    DistinctNaturalAndDriverPortWork : Set
    OriginalSourceAndAttribution : Set
    pins : SelectedOriginalPins
    switchTime : ActualSwitchOffEventTime
    electricalModes : CoherentElectricalModes
    acousticTransfer : MechanicalTransferFunction
    signedWork : DistinctNaturalAndDriverPortWork
    origin : OriginalSourceAndAttribution
