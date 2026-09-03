module DASHI.Analysis.RiemannG2HAProofCarryingRecoveryTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier

------------------------------------------------------------------------
-- PROOF-CARRYING H_A RECOVERY TRACE
--
-- Open textile PR #690 suggests a useful representation discipline: a visible
-- code is weaker than a proof-carrying edge, and every later edge should be
-- indexed by the state actually reached by the earlier ones.  This owner does
-- not import that open PR.  It applies the same already-repo-native dependent
-- trace discipline directly to the H_A recovery frontier.
--
-- Frontier.ProbeEnabled says which experiments are live.  RecoveryStep below
-- additionally says exactly how a successful experiment changes the recovery
-- state.  RecoveryPath then makes sequencing proof-relevant.
------------------------------------------------------------------------

data RecoveryStep :
  HA.HARecoveryState →
  HA.HARecoveryProbe →
  HA.HARecoveryState → Set where

  recoverImplementation :
    ∀ {action admissible hx formulaShift weilShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state HA.missing action admissible hx formulaShift weilShift provenance)
      HA.recoverImplementationIdentity
      (HA.ha-recovery-state HA.owned action admissible hx formulaShift weilShift provenance)

  recoverAction :
    ∀ {impl admissible hx formulaShift weilShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state impl HA.missing admissible hx formulaShift weilShift provenance)
      HA.recoverParameterizedAction
      (HA.ha-recovery-state impl HA.owned admissible hx formulaShift weilShift provenance)

  recoverAdmissibilityProof :
    ∀ {hx formulaShift weilShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state HA.owned HA.owned HA.missing hx formulaShift weilShift provenance)
      HA.recoverAdmissibility
      (HA.ha-recovery-state HA.owned HA.owned HA.owned hx formulaShift weilShift provenance)

  recoverHXAgreementProof :
    ∀ {admissible formulaShift weilShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state HA.owned HA.owned admissible HA.missing formulaShift weilShift provenance)
      HA.recoverCanonicalHXAgreement
      (HA.ha-recovery-state HA.owned HA.owned admissible HA.owned formulaShift weilShift provenance)

  recoverFormulaShiftProof :
    ∀ {admissible hx weilShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state HA.owned HA.owned admissible hx HA.missing weilShift provenance)
      HA.recoverSameFormulaSpectralShift
      (HA.ha-recovery-state HA.owned HA.owned admissible hx HA.owned weilShift provenance)

  recoverWeilShiftProof :
    ∀ {admissible hx formulaShift provenance} →
    RecoveryStep
      (HA.ha-recovery-state HA.owned HA.owned admissible hx formulaShift HA.missing provenance)
      HA.recoverSameWeilTransformShift
      (HA.ha-recovery-state HA.owned HA.owned admissible hx formulaShift HA.owned provenance)

  recoverProvenance :
    ∀ {impl action admissible hx formulaShift weilShift} →
    RecoveryStep
      (HA.ha-recovery-state impl action admissible hx formulaShift weilShift HA.anonymous)
      HA.recoverSourceProvenance
      (HA.ha-recovery-state impl action admissible hx formulaShift weilShift HA.sourceNative)

------------------------------------------------------------------------
-- Every proof-carrying step is admitted by the dependency frontier.
------------------------------------------------------------------------

stepWasEnabled :
  ∀ {before probe after} →
  RecoveryStep before probe after →
  Frontier.ProbeEnabled before probe
stepWasEnabled recoverImplementation = Frontier.implementationIdentityLive
stepWasEnabled recoverAction = Frontier.parameterizedActionLive
stepWasEnabled recoverAdmissibilityProof = Frontier.admissibilityLive
stepWasEnabled recoverHXAgreementProof = Frontier.canonicalHXAgreementLive
stepWasEnabled recoverFormulaShiftProof = Frontier.sameFormulaShiftLive
stepWasEnabled recoverWeilShiftProof = Frontier.sameWeilTransformShiftLive
stepWasEnabled recoverProvenance = Frontier.sourceProvenanceLive

------------------------------------------------------------------------
-- Dependent trace: the next edge starts at the actual state reached by the
-- previous edge.  No separate list of probe names can fake this property.
------------------------------------------------------------------------

data RecoveryPath : HA.HARecoveryState → HA.HARecoveryState → Set where
  recoveryDone :
    ∀ {state} → RecoveryPath state state

  recoveryThen :
    ∀ {start middle finish probe} →
    RecoveryStep start probe middle →
    RecoveryPath middle finish →
    RecoveryPath start finish

------------------------------------------------------------------------
-- Canonical independent-order witness.
--
-- Implementation identity and action are genuinely independent frontier
-- leaves: either order reaches the exact same two-receipt state.
------------------------------------------------------------------------

start : HA.HARecoveryState
start = Frontier.allMissingState

implementationAndActionOwned : HA.HARecoveryState
implementationAndActionOwned =
  HA.ha-recovery-state
    HA.owned HA.owned HA.missing HA.missing HA.missing HA.missing HA.anonymous

implementationThenAction : RecoveryPath start implementationAndActionOwned
implementationThenAction =
  recoveryThen recoverImplementation
    (recoveryThen recoverAction recoveryDone)

actionThenImplementation : RecoveryPath start implementationAndActionOwned
actionThenImplementation =
  recoveryThen recoverAction
    (recoveryThen recoverImplementation recoveryDone)

independentOrdersRejoinExactly :
  implementationAndActionOwned ≡ implementationAndActionOwned
independentOrdersRejoinExactly = refl

------------------------------------------------------------------------
-- Post-transport theorem consequences can likewise be ordered independently.
-- Here two representative orders are source-written explicitly.
------------------------------------------------------------------------

admissibilityAndHXOwned : HA.HARecoveryState
admissibilityAndHXOwned =
  HA.ha-recovery-state
    HA.owned HA.owned HA.owned HA.owned HA.missing HA.missing HA.anonymous

admissibilityThenHX :
  RecoveryPath implementationAndActionOwned admissibilityAndHXOwned
admissibilityThenHX =
  recoveryThen recoverAdmissibilityProof
    (recoveryThen recoverHXAgreementProof recoveryDone)

hxThenAdmissibility :
  RecoveryPath implementationAndActionOwned admissibilityAndHXOwned
hxThenAdmissibility =
  recoveryThen recoverHXAgreementProof
    (recoveryThen recoverAdmissibilityProof recoveryDone)

------------------------------------------------------------------------
-- Dependency no-go as a path-edge theorem.
------------------------------------------------------------------------

formulaShiftCannotBeFirstStep :
  ∀ {after} →
  RecoveryStep start HA.recoverSameFormulaSpectralShift after → ⊥
formulaShiftCannotBeFirstStep ()

weilShiftCannotBeFirstStep :
  ∀ {after} →
  RecoveryStep start HA.recoverSameWeilTransformShift after → ⊥
weilShiftCannotBeFirstStep ()

------------------------------------------------------------------------
-- Mathematical terminal versus source-audit terminal remain distinct.
------------------------------------------------------------------------

mathReadyAnonymous : HA.HARecoveryState
mathReadyAnonymous = HA.mathReadyAnonymous

fullyRecovered : HA.HARecoveryState
fullyRecovered = HA.mathReadySourceNative

provenanceAfterMathematics :
  RecoveryPath mathReadyAnonymous fullyRecovered
provenanceAfterMathematics =
  recoveryThen recoverProvenance recoveryDone

mathematicsMayTerminateBeforeAudit :
  Frontier.MathematicalHAClosed mathReadyAnonymous
mathematicsMayTerminateBeforeAudit = tt

sourceAuditStillOpenAtMathematicalTerminal :
  Frontier.SourceAuditClosed mathReadyAnonymous → ⊥
sourceAuditStillOpenAtMathematicalTerminal x = x

record HAProofCarryingRecoveryTraceBoundary : Set where
  constructor ha-proof-carrying-recovery-trace-boundary
  field
    bareProbeNameIsRecoveryProof : Bool
    bareProbeNameIsRecoveryProofIsFalse : bareProbeNameIsRecoveryProof ≡ false

    everyRecoveryEdgeCarriesItsExactSourceAndTargetState : Bool
    everyRecoveryEdgeCarriesItsExactSourceAndTargetStateIsTrue :
      everyRecoveryEdgeCarriesItsExactSourceAndTargetState ≡ true

    independentEnabledLeavesMayBeExecutedInDifferentOrders : Bool
    independentEnabledLeavesMayBeExecutedInDifferentOrdersIsTrue :
      independentEnabledLeavesMayBeExecutedInDifferentOrders ≡ true

    differentIndependentOrdersMayRejoinExactSameRecoveryState : Bool
    differentIndependentOrdersMayRejoinExactSameRecoveryStateIsTrue :
      differentIndependentOrdersMayRejoinExactSameRecoveryState ≡ true

    disabledDependencyEdgeCanAppearAsFirstProofCarryingStep : Bool
    disabledDependencyEdgeCanAppearAsFirstProofCarryingStepIsFalse :
      disabledDependencyEdgeCanAppearAsFirstProofCarryingStep ≡ false

    mathematicalTerminalMayPrecedeSourceAuditTerminal : Bool
    mathematicalTerminalMayPrecedeSourceAuditTerminalIsTrue :
      mathematicalTerminalMayPrecedeSourceAuditTerminal ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAProofCarryingRecoveryTraceBoundary :
  HAProofCarryingRecoveryTraceBoundary
canonicalHAProofCarryingRecoveryTraceBoundary =
  ha-proof-carrying-recovery-trace-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "Treat H_A recovery as a dependent proof-carrying trace, not a list of suggested probe names. Every successful recovery edge records the exact before/after evidence state and is certified to have been enabled by the dependency frontier. Independent leaves such as implementation identity and action may execute in either order and rejoin the same state; disabled formula/Weil-shift edges cannot appear before their transported-action prerequisites. Mathematical H_A closure may terminate before the independent provenance audit, which can continue as a later proof-carrying edge. This is search-state typing, not an RH proof."
