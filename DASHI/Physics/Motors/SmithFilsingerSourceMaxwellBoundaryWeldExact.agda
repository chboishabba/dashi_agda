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
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_)

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

-- Original provenance is a typed relation, not a string or an
-- implicit assertion that two historically different schematics coincide.
data SourceOwner : Bidi.Configuration → Time.SourceFamily → Set where
  ownerEarthReel :
    SourceOwner Bidi.filsingerEarthNarration Time.filsingerEarth
  ownerPortableProposal :
    SourceOwner Bidi.filsingerPortableProposal Time.filsingerPortable
  ownerSmithCompiled :
    SourceOwner Bidi.smithSuitcaseFigureTen Time.smithCompiled
  ownerKellyDarrerCompilation :
    SourceOwner Bidi.smithSuitcaseFigureTen Time.kellyDarrer

record SelectedBoundary : Set where
  constructor selectedBoundary
  field
    originalConfiguration : Bidi.Configuration
    originalSource : Time.SourceFamily
    sourceOwnerMatchesConfiguration :
      SourceOwner originalConfiguration originalSource
    sourcePort : Sun.SourcePort
    selectedRegime : Port.EnvironmentalSourceRegime
    selectedPhaseReference : Port.PhaseReference

-- The connection to existing symbolic field objects and finite flight is
-- explicit: it is not inferred from matching string labels.
record FormalFieldToPort (b : SelectedBoundary) : Set₂ where
  field
    symbolicField : Maxwell.MaxwellExteriorCalculusAdapter
    causalFlight : Time.RetardedFlight
    portWindow : Port.MidpointTwoPortWorkWindow

    -- A real member of the original typed time-indexed graph is included,
    -- with its source owner tied to the selected historical configuration.
    selectedMember : Time.MemberState
    memberSourceIsSelected :
      Time.MemberState.sourceOwner selectedMember
        ≡ SelectedBoundary.originalSource b

    -- Maxwell's symbolic curvature carrier must refer to the SAME
    -- explicitly selected member; do not equate arbitrary audio phases.
    selectedSymbolicCurvature : Maxwell.TwoForm
    memberFieldIsSelectedCurvature :
      Time.MemberState.symbolicField selectedMember
        ≡ selectedSymbolicCurvature

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
  (fieldPort : FormalFieldToPort b) : Set₂ where
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


-- The port cancellation weld is not merely an assumed duplicate cycle
-- receipt. It follows from SAME-PORT signed incoming/outgoing equations,
-- physical store return and the ORIGINAL two-port conservation equation.
-- No real-valued Maxwell theorem is implied by this finite Nat cancellation.
reorderIncidentWork :
  (nOut nReal cOut cReal stored : Nat) →
  ((nOut + nReal) + (cOut + cReal)) + stored
    ≡ ((nReal + cReal) + (nOut + cOut)) + stored
reorderIncidentWork no nr co cr s =
  solve 5
    (λ a b c d e →
      (((a :+ b) :+ (c :+ d)) :+ e)
        := (((b :+ d) :+ (a :+ c)) :+ e))
    refl no nr co cr s

reorderOutgoingWork :
  (load loss nOut cOut stored : Nat) →
  load + (loss + (nOut + (cOut + stored)))
    ≡ ((load + loss) + (nOut + cOut)) + stored
reorderOutgoingWork load loss no co s =
  solve 5
    (λ a b c d e →
      (a :+ (b :+ (c :+ (d :+ e))))
        := (((a :+ b) :+ (c :+ d)) :+ e))
    refl load loss no co s

-- Generic version of the exact port-to-cycle theorem.
-- This is a genuine derivation from independent port conservation and
-- signed source/control incident/outgoing identifications.
signedPortBalanceAfterFullStoreReturn :
  (nIncident cIncident nOutgoing cOutgoing
   nNet cNet initial final load loss : Nat) →
  nIncident ≡ nOutgoing + nNet →
  cIncident ≡ cOutgoing + cNet →
  initial ≡ final →
  (nIncident + cIncident) + initial
    ≡ load + (loss + (nOutgoing + (cOutgoing + final))) →
  nNet + cNet ≡ load + loss
signedPortBalanceAfterFullStoreReturn
  ni ci no co nn cn initial final load loss
  naturalLaw controllerLaw storeLaw boundaryLaw =
  Cycle.+-cancelRight _ _ (no + co)
    (Cycle.+-cancelRight _ _ final
      (Cycle.trans
        (Bound.sym (reorderIncidentWork no nn co cn final))
        (Cycle.trans
          (Cycle.cong
            (λ n → (n + (co + cn)) + final)
            (Bound.sym naturalLaw))
          (Cycle.trans
            (Cycle.cong
              (λ c → (ni + c) + final)
              (Bound.sym controllerLaw))
            (Cycle.trans
              (Cycle.cong
                (λ stored → (ni + ci) + stored)
                (Bound.sym storeLaw))
              (Cycle.trans boundaryLaw
                (reorderOutgoingWork load loss no co final)))))))

-- The result is *actually* about the signed two-port window, independent
-- of separately asserting a RepeatableSourceCycle ledger. This is the
-- missing formal signed-port → replenishment bookkeeping weld.
signedNaturalAndControllerWorkPaysSamePortLoad :
  (b : SelectedBoundary)
  (f : FormalFieldToPort b)
  (w : SignedSourceCycleWeld b f) →
  Cycle.RepeatableSourceCycle.naturalSourceWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (SignedSourceCycleWeld.cycleWithSourceCap w))
  + Cycle.RepeatableSourceCycle.controllerWork
    (Cycle.AdmittedSourceCapCycle.repeatable
      (SignedSourceCycleWeld.cycleWithSourceCap w))
  ≡ Port.MidpointTwoPortWorkWindow.usefulWork
      (FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.internalLoss
        (FormalFieldToPort.portWindow f)
signedNaturalAndControllerWorkPaysSamePortLoad b f w =
  signedPortBalanceAfterFullStoreReturn
    (Port.MidpointTwoPortWorkWindow.naturalIncident
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.controllerIncident
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.naturalOutgoing
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.controllerOutgoing
      (FormalFieldToPort.portWindow f))
    (Cycle.RepeatableSourceCycle.naturalSourceWork
      (Cycle.AdmittedSourceCapCycle.repeatable
        (SignedSourceCycleWeld.cycleWithSourceCap w)))
    (Cycle.RepeatableSourceCycle.controllerWork
      (Cycle.AdmittedSourceCapCycle.repeatable
        (SignedSourceCycleWeld.cycleWithSourceCap w)))
    (Port.MidpointTwoPortWorkWindow.initialStored
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.finalStored
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (FormalFieldToPort.portWindow f))
    (Port.MidpointTwoPortWorkWindow.internalLoss
      (FormalFieldToPort.portWindow f))
    (SignedSourceCycleWeld.naturalIncidentPaysOutgoingAndSourceWork w)
    (SignedSourceCycleWeld.controllerIncidentPaysOutgoingAndControllerWork w)
    (SignedSourceCycleWeld.sameOriginalStoreReturns w)
    (Port.MidpointTwoPortWorkWindow.completeBoundaryBalance
      (FormalFieldToPort.portWindow f))

-- Independent proof: useful work cannot exceed the signed net incoming
-- natural+controller work when all fields/stores return on the same cycle.
signedPortLoadBoundAfterStoreReturn :
  (b : SelectedBoundary)
  (f : FormalFieldToPort b)
  (w : SignedSourceCycleWeld b f) →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (FormalFieldToPort.portWindow f))
    (Cycle.RepeatableSourceCycle.naturalSourceWork
      (Cycle.AdmittedSourceCapCycle.repeatable
        (SignedSourceCycleWeld.cycleWithSourceCap w))
      + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (SignedSourceCycleWeld.cycleWithSourceCap w)))
signedPortLoadBoundAfterStoreReturn b f w =
  Bound.transportUpper
    (Bound.sym (signedNaturalAndControllerWorkPaysSamePortLoad b f w))
    (Bound.≤-append
      (Port.MidpointTwoPortWorkWindow.usefulWork
        (FormalFieldToPort.portWindow f))
      (Port.MidpointTwoPortWorkWindow.internalLoss
        (FormalFieldToPort.portWindow f)))
