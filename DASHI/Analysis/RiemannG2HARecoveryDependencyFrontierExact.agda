module DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Active

------------------------------------------------------------------------
-- DEPENDENCY FRONTIER SUPERSEDES A SINGLE LINEAR H_A PROBE ORDER
--
-- The first #691 owner used a deterministic "first missing" scheduler.  That
-- is safe as a serial search policy, but it is stronger than the mathematical
-- dependency graph actually requires.  Cross-pollinating the merged Aristotle
-- AND/OR active-search discipline, this owner exposes the live probe FRONTIER:
-- independent receipts may be recovered in parallel, while downstream shift
-- proofs remain disabled until the transported action exists.
--
-- The consumer quotient from the first #691 owner also has a concrete
-- consequence here: mathematical H_A compilation cannot be made to wait for
-- provenance, because provenance-only variation is invisible to that consumer.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Two independent closure consumers.
------------------------------------------------------------------------

MathematicalHAClosed : HA.HARecoveryState → Set
MathematicalHAClosed
  (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.owned HA.owned provenance) = ⊤
MathematicalHAClosed state = ⊥

SourceAuditClosed : HA.HARecoveryState → Set
SourceAuditClosed
  (HA.ha-recovery-state impl action admissible hx formulaShift weilShift HA.sourceNative) = ⊤
SourceAuditClosed state = ⊥

provenanceOnlyState : HA.HARecoveryState
provenanceOnlyState =
  HA.ha-recovery-state
    HA.missing HA.missing HA.missing HA.missing HA.missing HA.missing HA.sourceNative

mathReadyAnonymousIsMathematicallyClosed :
  MathematicalHAClosed HA.mathReadyAnonymous
mathReadyAnonymousIsMathematicallyClosed = tt

mathReadyAnonymousSourceAuditStillOpen :
  SourceAuditClosed HA.mathReadyAnonymous → ⊥
mathReadyAnonymousSourceAuditStillOpen x = x

provenanceOnlySourceAuditClosed :
  SourceAuditClosed provenanceOnlyState
provenanceOnlySourceAuditClosed = tt

provenanceOnlyMathematicsStillOpen :
  MathematicalHAClosed provenanceOnlyState → ⊥
provenanceOnlyMathematicsStillOpen x = x

------------------------------------------------------------------------
-- 2. Dependency-aware enabled probe relation.
--
-- Implementation identity and source-native action may be recovered in
-- parallel.  Once both exist, the four theorem-bearing action consequences may
-- also be pursued independently.  Provenance is a separate audit coordinate.
-- Compilation is enabled exactly when the six mathematical receipts are owned,
-- regardless of provenance.
------------------------------------------------------------------------

data ProbeEnabled : HA.HARecoveryState → HA.HARecoveryProbe → Set where
  implementationIdentityLive :
    ∀ {action admissible hx formulaShift weilShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.missing action admissible hx formulaShift weilShift provenance)
      HA.recoverImplementationIdentity

  parameterizedActionLive :
    ∀ {impl admissible hx formulaShift weilShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state impl HA.missing admissible hx formulaShift weilShift provenance)
      HA.recoverParameterizedAction

  admissibilityLive :
    ∀ {hx formulaShift weilShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.owned HA.owned HA.missing hx formulaShift weilShift provenance)
      HA.recoverAdmissibility

  canonicalHXAgreementLive :
    ∀ {admissible formulaShift weilShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.owned HA.owned admissible HA.missing formulaShift weilShift provenance)
      HA.recoverCanonicalHXAgreement

  sameFormulaShiftLive :
    ∀ {admissible hx weilShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.owned HA.owned admissible hx HA.missing weilShift provenance)
      HA.recoverSameFormulaSpectralShift

  sameWeilTransformShiftLive :
    ∀ {admissible hx formulaShift provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.owned HA.owned admissible hx formulaShift HA.missing provenance)
      HA.recoverSameWeilTransformShift

  sourceProvenanceLive :
    ∀ {impl action admissible hx formulaShift weilShift} →
    ProbeEnabled
      (HA.ha-recovery-state impl action admissible hx formulaShift weilShift HA.anonymous)
      HA.recoverSourceProvenance

  compileMathematicalHALive :
    ∀ {provenance} →
    ProbeEnabled
      (HA.ha-recovery-state HA.owned HA.owned HA.owned HA.owned HA.owned HA.owned provenance)
      HA.compileProofRelevantHA

------------------------------------------------------------------------
-- 3. Concrete frontier witnesses.
------------------------------------------------------------------------

allMissingState : HA.HARecoveryState
allMissingState =
  HA.ha-recovery-state
    HA.missing HA.missing HA.missing HA.missing HA.missing HA.missing HA.anonymous

implementationAndActionParallelAtStart :
  ProbeEnabled allMissingState HA.recoverImplementationIdentity ×
  ProbeEnabled allMissingState HA.recoverParameterizedAction
implementationAndActionParallelAtStart =
  implementationIdentityLive , parameterizedActionLive

provenanceAlsoIndependentAtStart :
  ProbeEnabled allMissingState HA.recoverSourceProvenance
provenanceAlsoIndependentAtStart = sourceProvenanceLive

formulaShiftBlockedBeforeTransportedAction :
  ProbeEnabled allMissingState HA.recoverSameFormulaSpectralShift → ⊥
formulaShiftBlockedBeforeTransportedAction ()

postTransportState : HA.HARecoveryState
postTransportState =
  HA.ha-recovery-state
    HA.owned HA.owned HA.missing HA.missing HA.missing HA.missing HA.anonymous

fourProofConsequencesParallelAfterTransport :
  ProbeEnabled postTransportState HA.recoverAdmissibility ×
  (ProbeEnabled postTransportState HA.recoverCanonicalHXAgreement ×
  (ProbeEnabled postTransportState HA.recoverSameFormulaSpectralShift ×
   ProbeEnabled postTransportState HA.recoverSameWeilTransformShift))
fourProofConsequencesParallelAfterTransport =
  admissibilityLive ,
  (canonicalHXAgreementLive ,
  (sameFormulaShiftLive , sameWeilTransformShiftLive))

mathReadyAnonymousMayCompileWithoutProvenance :
  ProbeEnabled HA.mathReadyAnonymous HA.compileProofRelevantHA
mathReadyAnonymousMayCompileWithoutProvenance = compileMathematicalHALive

mathReadyAnonymousMayAlsoContinueSourceAudit :
  ProbeEnabled HA.mathReadyAnonymous HA.recoverSourceProvenance
mathReadyAnonymousMayAlsoContinueSourceAudit = sourceProvenanceLive

------------------------------------------------------------------------
-- 4. Active-search cross-pollination.
------------------------------------------------------------------------

activeSearchAllowsOutcomeAdaptiveBranching :
  Active.nextDiscriminatorMayDependOnPreviousOutcome
    Active.canonicalActiveExperimentalProofSearchBoundary ≡ true
activeSearchAllowsOutcomeAdaptiveBranching =
  Active.nextDiscriminatorMayDependOnPreviousOutcomeIsTrue
    Active.canonicalActiveExperimentalProofSearchBoundary

------------------------------------------------------------------------
-- 5. Boundary.
------------------------------------------------------------------------

record HARecoveryDependencyFrontierBoundary : Set where
  constructor ha-recovery-dependency-frontier-boundary
  field
    oneLinearProbeOrderIsMathematicallyRequired : Bool
    oneLinearProbeOrderIsMathematicallyRequiredIsFalse :
      oneLinearProbeOrderIsMathematicallyRequired ≡ false

    implementationIdentityAndActionMayBeRecoveredInParallel : Bool
    implementationIdentityAndActionMayBeRecoveredInParallelIsTrue :
      implementationIdentityAndActionMayBeRecoveredInParallel ≡ true

    postTransportProofConsequencesMayBeRecoveredInParallel : Bool
    postTransportProofConsequencesMayBeRecoveredInParallelIsTrue :
      postTransportProofConsequencesMayBeRecoveredInParallel ≡ true

    provenanceMustCloseBeforeMathematicalHACompilation : Bool
    provenanceMustCloseBeforeMathematicalHACompilationIsFalse :
      provenanceMustCloseBeforeMathematicalHACompilation ≡ false

    mathematicalClosureAutomaticallyClosesSourceAudit : Bool
    mathematicalClosureAutomaticallyClosesSourceAuditIsFalse :
      mathematicalClosureAutomaticallyClosesSourceAudit ≡ false

    sourceAuditClosureAutomaticallyClosesHAMathematics : Bool
    sourceAuditClosureAutomaticallyClosesHAMathematicsIsFalse :
      sourceAuditClosureAutomaticallyClosesHAMathematics ≡ false

    dependencyFrontierShouldReplaceFirstMissingSchedulerForRanking : Bool
    dependencyFrontierShouldReplaceFirstMissingSchedulerForRankingIsTrue :
      dependencyFrontierShouldReplaceFirstMissingSchedulerForRanking ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHARecoveryDependencyFrontierBoundary :
  HARecoveryDependencyFrontierBoundary
canonicalHARecoveryDependencyFrontierBoundary =
  ha-recovery-dependency-frontier-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    "Replace the serial first-missing H_A search order by the actual dependency frontier. Source implementation identity and source-native action are independent recoveries; after both are owned, admissibility, canonical-H_X agreement, same-formula spectral shift and same-Weil-transform shift are parallel theorem consequences. Provenance remains an independent source-audit coordinate. Because the mathematical H_A consumer quotients provenance-only variation, a mathematically complete anonymous state may compile H_A while source audit remains open. Use hard prerequisites to define the live frontier, then rank only among enabled probes. This changes search scheduling only and does not inhabit any missing analytic theorem or derive RH."
