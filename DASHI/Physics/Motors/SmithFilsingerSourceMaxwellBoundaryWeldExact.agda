module DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact where

-- Source-qualified formal WELD; NOT a simulation or an original-device proof.
-- Composes existing MAXWELL authority, retarded clock, source selection,
-- signed natural/controller ports and exact restored-cycle energy bound.
--
-- This is a consumer of previous owners. It does not promote the symbolic
-- Maxwell source-current or Hodge equation to a physical solution.
-- User-origin claim: internally controlled source/sink phase may regulate
-- access to independently replenished Earth/atmospheric power.
--
-- The necessary physical equalities remain EXPLICIT fields, not postulates.
-- In particular the two-port signed natural input is not magically
-- inferred from an arbitrary field or from a phase observation.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.SmithFilsingerReflectedPortBidiExact as Bidi
import DASHI.Physics.Motors.SmithFilsingerSunEarthCoupledSourceExact as Sun
import DASHI.Physics.Motors.SmithFilsingerFinitePhaseMatchingExact as Phase
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

-- A *data-carrying* stage index prevents attaching a proof for a different
-- original configuration / source family by moving between field records.
-- The Smith suitcase, Filsinger Earth reel and portable proposal are
-- distinct configuration constructors in the existing Bidi owner.

record SelectedBoundary : Set where
  constructor selectedBoundary
  field
    originalConfiguration : Bidi.Configuration
    originalSource : Time.SourceFamily
    sourcePort : Sun.SourcePort
    selectedRegime : Port.EnvironmentalSourceRegime
    selectedPhaseReference : Port.PhaseReference

-- The connection to existing symbolic field objects and finite flight is
-- explicit: it is not inferred from matching string labels.
record FormalFieldToPort (b : SelectedBoundary) : Set₁ where
  field
    symbolicField : Maxwell.MaxwellExteriorCalculusAdapter
    causalFlight : Time.RetardedFlight
    portWindow : Port.MidpointTwoPortWorkWindow
    originalMaxwellSourceCurrent : Set
    originalRetardedMaterialResponse : Set
    originalPortFieldFluxEquality : Set
    sourceCurrent : originalMaxwellSourceCurrent
    response : originalRetardedMaterialResponse
    fieldToPort : originalPortFieldFluxEquality

-- The actual energy weld cannot be inhabited by the symbolic Maxwell
-- adapter alone. It requires a *separate* same-boundary real-work
-- identification for every input/output and for source replenishment.
-- All observational obligations are explicitly indexed by one selected
-- configuration b.
record SignedSourceCycleWeld
  (b : SelectedBoundary)
  (fieldPort : FormalFieldToPort b) : Set₁ where
  field
    cycleWithSourceCap : Cycle.AdmittedSourceCapCycle

    -- Port net work is signed: incident - outgoing.  The source and
    -- controller cycles are linked to the ORIGINAL same selected ports.
    naturalIncidentPaysOutgoingAndSourceWork :
      Port.MidpointTwoPortWorkWindow.naturalIncident
        (FormalFieldToPort.portWindow fieldPort)
      ≡ Port.MidpointTwoPortWorkWindow.naturalOutgoing
        (FormalFieldToPort.portWindow fieldPort)
          + Cycle.RepeatableSourceCycle.naturalSourceWork
              (Cycle.AdmittedSourceCapCycle.repeatable cycleWithSourceCap)

    controllerIncidentPaysOutgoingAndControllerWork :
      Port.MidpointTwoPortWorkWindow.controllerIncident
        (FormalFieldToPort.portWindow fieldPort)
      ≡ Port.MidpointTwoPortWorkWindow.controllerOutgoing
        (FormalFieldToPort.portWindow fieldPort)
          + Cycle.RepeatableSourceCycle.controllerWork
              (Cycle.AdmittedSourceCapCycle.repeatable cycleWithSourceCap)

    sameOriginalUsefulLoad :
      Port.MidpointTwoPortWorkWindow.usefulWork
        (FormalFieldToPort.portWindow fieldPort)
      ≡ Cycle.RepeatableSourceCycle.usefulLoadWork
          (Cycle.AdmittedSourceCapCycle.repeatable cycleWithSourceCap)

    sameOriginalInternalLoss :
      Port.MidpointTwoPortWorkWindow.internalLoss
        (FormalFieldToPort.portWindow fieldPort)
      ≡ Cycle.RepeatableSourceCycle.allHeatAndOutgoing
          (Cycle.AdmittedSourceCapCycle.repeatable cycleWithSourceCap)

    sameOriginalStoreReturns :
      Port.MidpointTwoPortWorkWindow.initialStored
        (FormalFieldToPort.portWindow fieldPort)
      ≡ Port.MidpointTwoPortWorkWindow.finalStored
        (FormalFieldToPort.portWindow fieldPort)

    -- A required reference to the existing source-qualified physical
    -- evidence owner. No such value was constructed from the audio/plates.
    originalEnvironmentalEvidence :
      Cycle.SameOriginalCycleAdmission

-- The proof really transports the existing independently admitted source
-- cap through the identity of the *same original load port*, rather than
-- merely redeclaring the bound or restating its premise as a result.
sourceCapTransfersToSameOriginalPort :
  (b : SelectedBoundary)
  (f : FormalFieldToPort b)
  (w : SignedSourceCycleWeld b f) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (FormalFieldToPort.portWindow f))
    (Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
      (SignedSourceCycleWeld.cycleWithSourceCap w)
     + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (SignedSourceCycleWeld.cycleWithSourceCap w)))
sourceCapTransfersToSameOriginalPort b f w =
  Bound.transportUpper refl
    (substLower
      (SignedSourceCycleWeld.sameOriginalUsefulLoad w)
      (Cycle.replenishedLoadBelowNaturalCapPlusController
        (SignedSourceCycleWeld.cycleWithSourceCap w)))
  where
    substLower : {a b c : Nat} → a ≡ b → Bound._≤_ b c → Bound._≤_ a c
    substLower refl p = p

-- A no-natural-incident source has no *strictly positive* natural net
-- port work; the proof consumes the earlier finite source-off negative
-- control instead of reimplementing an order or port-sign convention.
sourceOffExcludesPositiveNaturalNet :
  (b : SelectedBoundary)
  (f : FormalFieldToPort b) →
  Port.MidpointTwoPortWorkWindow.naturalIncident
    (FormalFieldToPort.portWindow f) ≡ zero →
  Phase.PositiveNaturalNet (FormalFieldToPort.portWindow f) →
  Port.Contradiction
sourceOffExcludesPositiveNaturalNet b f sourceOff positive =
  Phase.naturalOffCannotSupplyPositiveNet
    (FormalFieldToPort.portWindow f) sourceOff positive

-- A source-side clock cannot, by itself, prove a physically received
-- phase: use the actual indexed causal-flight result of the original
-- time-indexed owner.
fieldPortArrivalNotBeforeLaunch :
  (b : SelectedBoundary) (f : FormalFieldToPort b) →
  Bound._≤_
    (Time.RetardedFlight.launch (FormalFieldToPort.causalFlight f))
    (Time.RetardedFlight.arrival (FormalFieldToPort.causalFlight f))
fieldPortArrivalNotBeforeLaunch b f =
  Time.arrivalNoEarlier (FormalFieldToPort.causalFlight f)

-- Explicit anti-promotion: the canonical Maxwell adapter's field equation
-- is still authority-bound, not a solved physical source equation.
symbolicMaxwellIsNotPhysicalAdmission :
  Maxwell.MaxwellExteriorCalculusAdapter.maxwellFieldEquationPromoted
    Maxwell.canonicalMaxwellExteriorCalculusAdapter ≡ false
symbolicMaxwellIsNotPhysicalAdmission = refl

-- Exact selected discrete phase cancellation is already a theorem in the
-- finite-phase owner; import it rather than creating a duplicate proof.
complementaryFinitePhasesPreserveTotal :
  (slot : Phase.Slot) (base excursion : Nat) →
  Phase.branchOne slot base excursion
    + Phase.branchTwo slot base excursion
  ≡ Phase.high base excursion + base
complementaryFinitePhasesPreserveTotal =
  Phase.complementaryConstantTotal
