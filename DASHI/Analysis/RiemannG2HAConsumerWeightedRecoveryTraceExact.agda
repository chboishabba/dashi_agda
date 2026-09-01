module DASHI.Analysis.RiemannG2HAConsumerWeightedRecoveryTraceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier
import DASHI.Analysis.RiemannG2HAProofCarryingRecoveryTraceExact as Trace
import DASHI.Analysis.RiemannG2HAConsumerFanoutPriorityExact as Priority

------------------------------------------------------------------------
-- CONSUMER-WEIGHTED, PROOF-CARRYING RECOVERY
--
-- Priority is not a free-standing recommendation.  A selected move must still
-- be a literal RecoveryStep on the exact current state.  Conversely a valid
-- recovery edge need not be highest-fanout: fanout is a planning coordinate,
-- not theorem authority.
------------------------------------------------------------------------

record WeightedRecoveryStep
    (before : HA.HARecoveryState)
    (probe : HA.HARecoveryProbe)
    (after : HA.HARecoveryState) : Set where
  constructor weighted-recovery-step
  field
    recovery : Trace.RecoveryStep before probe after
    priorityCandidate : Priority.PriorityCandidate before probe

open WeightedRecoveryStep public

weightedStepEnabled :
  ∀ {before probe after} →
  WeightedRecoveryStep before probe after →
  Frontier.ProbeEnabled before probe
weightedStepEnabled step = Priority.enabled (priorityCandidate step)

weightedStepScore :
  ∀ {before probe after} →
  WeightedRecoveryStep before probe after → Nat
weightedStepScore {probe = probe} step = Priority.probeFanoutScore probe

------------------------------------------------------------------------
-- Initial top-fanout recovery edges.
------------------------------------------------------------------------

implementationAfterStart : HA.HARecoveryState
implementationAfterStart =
  HA.ha-recovery-state
    HA.owned HA.missing HA.missing HA.missing HA.missing HA.missing HA.anonymous

actionAfterStart : HA.HARecoveryState
actionAfterStart =
  HA.ha-recovery-state
    HA.missing HA.owned HA.missing HA.missing HA.missing HA.missing HA.anonymous

weightedImplementationFirst :
  WeightedRecoveryStep
    Frontier.allMissingState
    HA.recoverImplementationIdentity
    implementationAfterStart
weightedImplementationFirst =
  weighted-recovery-step
    Trace.recoverImplementation
    Priority.initialImplementationPriority

weightedActionFirst :
  WeightedRecoveryStep
    Frontier.allMissingState
    HA.recoverParameterizedAction
    actionAfterStart
weightedActionFirst =
  weighted-recovery-step
    Trace.recoverAction
    Priority.initialActionPriority

weightedImplementationFirstScoreIsFive :
  weightedStepScore weightedImplementationFirst
  ≡ suc (suc (suc (suc (suc zero))))
weightedImplementationFirstScoreIsFive = refl

weightedActionFirstScoreIsFive :
  weightedStepScore weightedActionFirst
  ≡ suc (suc (suc (suc (suc zero))))
weightedActionFirstScoreIsFive = refl

------------------------------------------------------------------------
-- An enabled lower-fanout audit edge remains lawful.  Highest-alpha ranking
-- does not erase it; it merely says it is not one of the current mathematical
-- top-fanout moves.
------------------------------------------------------------------------

provenanceAfterStart : HA.HARecoveryState
provenanceAfterStart =
  HA.ha-recovery-state
    HA.missing HA.missing HA.missing HA.missing HA.missing HA.missing HA.sourceNative

weightedProvenanceFirst :
  WeightedRecoveryStep
    Frontier.allMissingState
    HA.recoverSourceProvenance
    provenanceAfterStart
weightedProvenanceFirst =
  weighted-recovery-step
    Trace.recoverProvenance
    Priority.initialProvenancePriority

weightedProvenanceFirstScoreIsOne :
  weightedStepScore weightedProvenanceFirst ≡ suc zero
weightedProvenanceFirstScoreIsOne = refl

------------------------------------------------------------------------
-- Disabled high-level theorem probes cannot be smuggled in by attaching a
-- ranking receipt: there is no RecoveryStep and no PriorityCandidate at start.
------------------------------------------------------------------------

formulaShiftCannotBeWeightedFirstStep :
  ∀ {after} →
  WeightedRecoveryStep
    Frontier.allMissingState
    HA.recoverSameFormulaSpectralShift
    after → ⊥
formulaShiftCannotBeWeightedFirstStep step =
  Trace.formulaShiftCannotBeFirstStep (recovery step)

weilShiftCannotBeWeightedFirstStep :
  ∀ {after} →
  WeightedRecoveryStep
    Frontier.allMissingState
    HA.recoverSameWeilTransformShift
    after → ⊥
weilShiftCannotBeWeightedFirstStep step =
  Trace.weilShiftCannotBeFirstStep (recovery step)

------------------------------------------------------------------------
-- Top-fanout is a property of a lawful step, not a replacement for one.
------------------------------------------------------------------------

TopFanoutWeightedInitialStep :
  ∀ {probe after} →
  WeightedRecoveryStep Frontier.allMissingState probe after → Set
TopFanoutWeightedInitialStep {probe = probe} step =
  Priority.probeFanoutScore probe
  ≡ suc (suc (suc (suc (suc zero))))

implementationWeightedStepIsTopFanout :
  TopFanoutWeightedInitialStep weightedImplementationFirst
implementationWeightedStepIsTopFanout = refl

actionWeightedStepIsTopFanout :
  TopFanoutWeightedInitialStep weightedActionFirst

actionWeightedStepIsTopFanout = refl

provenanceWeightedStepIsNotTopFanout :
  TopFanoutWeightedInitialStep weightedProvenanceFirst → ⊥
provenanceWeightedStepIsNotTopFanout ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HAConsumerWeightedRecoveryBoundary : Set where
  constructor ha-consumer-weighted-recovery-boundary
  field
    priorityReceiptCanReplaceRecoveryProof : Bool
    priorityReceiptCanReplaceRecoveryProofIsFalse :
      priorityReceiptCanReplaceRecoveryProof ≡ false

    validRecoveryEdgeAutomaticallyHasHighestFanout : Bool
    validRecoveryEdgeAutomaticallyHasHighestFanoutIsFalse :
      validRecoveryEdgeAutomaticallyHasHighestFanout ≡ false

    disabledProbeCanBecomeWeightedStepByHighPriorityLabel : Bool
    disabledProbeCanBecomeWeightedStepByHighPriorityLabelIsFalse :
      disabledProbeCanBecomeWeightedStepByHighPriorityLabel ≡ false

    implementationAndActionAreBothTopFanoutProofCarryingInitialMoves : Bool
    implementationAndActionAreBothTopFanoutProofCarryingInitialMovesIsTrue :
      implementationAndActionAreBothTopFanoutProofCarryingInitialMoves ≡ true

    provenanceRemainsLawfulEvenWhenLowerMathematicalFanout : Bool
    provenanceRemainsLawfulEvenWhenLowerMathematicalFanoutIsTrue :
      provenanceRemainsLawfulEvenWhenLowerMathematicalFanout ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHAConsumerWeightedRecoveryBoundary :
  HAConsumerWeightedRecoveryBoundary
canonicalHAConsumerWeightedRecoveryBoundary =
  ha-consumer-weighted-recovery-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    "Compose the H_A fanout heuristic with the dependent recovery trace rather than letting either replace the other. Implementation identity and source-native action are both lawful proof-carrying first moves and both occupy the declared five-consumer top fanout. Source provenance is also a lawful first recovery edge but remains a one-consumer audit move. Formula and Weil shift cannot become first moves merely by receiving a priority label because no proof-carrying recovery edge exists before transport. Search priority therefore ranks lawful edges; it never manufactures them, and RH is not derived."
