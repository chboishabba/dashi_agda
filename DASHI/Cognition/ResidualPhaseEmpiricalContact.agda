module DASHI.Cognition.ResidualPhaseEmpiricalContact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ContactHamiltonian as Hamiltonian
import DASHI.Core.EmpiricalContactReceipt as Receipt
import DASHI.Core.ObservableContactGeometry as Observable

open Receipt public using
  ( EmpiricalContactReceipt
  ; ReplayArtifact
  ; SourceBinding
  )

------------------------------------------------------------------------
-- Lightweight witness type
------------------------------------------------------------------------

record Witness : Set where
  constructor witness

------------------------------------------------------------------------
-- Residual-phase carrier and observable vocabulary
------------------------------------------------------------------------

record ResidualPhaseCarrier : Set where
  constructor residualPhaseCarrier
  field
    hiddenBranchState : String
    publicTraceHandle : String

record TraceEvent : Set where
  constructor traceEvent
  field
    eventIndex : Nat
    eventLabel : String

record PublicSplit : Set where
  constructor publicSplit
  field
    splitTag : String

record BranchStep : Set where
  constructor branchStep
  field
    stepIndex : Nat

record BranchDepth : Set where
  constructor branchDepth
  field
    depthValue : Nat

data TransitionClass : Set where
  stableTransition    : TransitionClass
  branchingTransition : TransitionClass
  mismatchTransition  : TransitionClass
  fixationTransition  : TransitionClass

record TransitionObservation : Set where
  constructor transitionObservation
  field
    fromEvent       : TraceEvent
    toEvent         : TraceEvent
    transitionClass : TransitionClass

record PublicLabel : Set where
  constructor publicLabel
  field
    labelText : String

record LocalContext : Set where
  constructor localContext
  field
    contextTag : String

record ResidualMismatch : Set where
  constructor residualMismatch
  field
    mismatchLabel : PublicLabel
    leftContext   : LocalContext
    rightContext  : LocalContext

record PrivateLexemeRecurrence : Set where
  constructor privateLexemeRecurrence
  field
    recurrenceToken : String

record FixationMarker : Set where
  constructor fixationMarker
  field
    markerLabel : String

record AuthorityPromotionBlocked : Set where
  constructor authorityPromotionBlocked
  field
    empiricalAuthorityBlocked            : Bool
    clinicalOrMetaphysicalBlocked        : Bool

------------------------------------------------------------------------
-- Abstract core instantiations
------------------------------------------------------------------------

carrierProjection : ResidualPhaseCarrier → TraceEvent
carrierProjection carrier =
  traceEvent 0 (ResidualPhaseCarrier.publicTraceHandle carrier)

carrierFibre : TraceEvent → Set
carrierFibre observable = ResidualPhaseCarrier

traceProjection : TraceEvent → TraceEvent
traceProjection event = event

traceTransition : TraceEvent → TraceEvent → Set
traceTransition left right = Witness

traceResidual : TraceEvent → TraceEvent → Set
traceResidual left right = ResidualMismatch

traceComparisonLaw : TraceEvent → TraceEvent → Set
traceComparisonLaw left right = Witness

ResidualPhaseObservableContactGeometry :
  Observable.ObservableContactGeometry
ResidualPhaseObservableContactGeometry =
  Observable.observableContactGeometry
    ResidualPhaseCarrier
    TraceEvent
    TraceEvent
    ResidualMismatch
    carrierProjection
    carrierFibre
    traceProjection
    traceResidual
    traceComparisonLaw
    (λ mismatch observable → Witness)
    true
    false
    traceTransition
    Witness

record TracePressure : Set where
  constructor tracePressure
  field
    mismatchPressure          : Bool
    instabilityPressure       : Bool
    fixationPressure          : Bool
    privateLexemeDriftPressure : Bool
    compressionCertaintyRisk  : Bool

traceHamiltonian : ResidualMismatch → TracePressure
traceHamiltonian mismatch =
  tracePressure true true true true true

tracePressureWitness : TracePressure → Set
tracePressureWitness pressure = Witness

traceAuthorityPenaltyWitness : TracePressure → Set
traceAuthorityPenaltyWitness pressure = Witness

ResidualPhaseContactHamiltonian :
  Hamiltonian.ContactHamiltonian
ResidualPhaseContactHamiltonian =
  Hamiltonian.contactHamiltonian
    ResidualMismatch
    TracePressure
    traceHamiltonian
    tracePressureWitness
    traceAuthorityPenaltyWitness
    true

------------------------------------------------------------------------
-- Theorem surfaces for the cognition-specific instantiation
------------------------------------------------------------------------

PublicSplitIsObservable : PublicSplit → Set
PublicSplitIsObservable split = Witness

BranchDepthIsDyadicContact : BranchStep → BranchDepth → Set
BranchDepthIsDyadicContact step depth = Witness

ResidualMismatchIsFibreEvidence :
  PublicLabel → LocalContext → LocalContext → Set
ResidualMismatchIsFibreEvidence label left right = Witness

TransitionPatternIsTemporalContact :
  TraceEvent → TraceEvent → TransitionClass → Set
TransitionPatternIsTemporalContact left right transitionClass = Witness

FixationMarkerBlocksAuthority : FixationMarker → AuthorityPromotionBlocked
FixationMarkerBlocksAuthority marker =
  authorityPromotionBlocked false false

data SymbolicRecurrence : Set where
  recurrence369       : SymbolicRecurrence
  recurrencePrimorial : SymbolicRecurrence
  recurrenceChaos     : SymbolicRecurrence

symbolicRecurrenceEmpiricalAuthority : SymbolicRecurrence → Bool
symbolicRecurrenceEmpiricalAuthority recurrence = false

SymbolicRecurrenceNoEmpiricalAuthority :
  (recurrence : SymbolicRecurrence) →
  symbolicRecurrenceEmpiricalAuthority recurrence ≡ false
SymbolicRecurrenceNoEmpiricalAuthority recurrence = refl

------------------------------------------------------------------------
-- Canonical generic receipt instantiated for the residual-phase trace lane
------------------------------------------------------------------------

canonicalSourceBinding : SourceBinding
canonicalSourceBinding =
  Receipt.sourceBinding
    "uploaded tlurey trace"
    "trace-source"
    "TlureyDyadicNonaryTraceReceipt.canonicalTraceReceipt"

canonicalReplayArtifact : ReplayArtifact
canonicalReplayArtifact =
  Receipt.replayArtifact
    "canonical tlurey trace replay handle"
    "DASHI/Cognition/TlureyDyadicNonaryTraceReceipt.agda"
    "scripts/run_agda29_parallel_check.sh DASHI/Cognition/TlureyDyadicNonaryTraceReceipt.agda"

canonicalEmpiricalContactReceipt : EmpiricalContactReceipt
canonicalEmpiricalContactReceipt =
  Receipt.canonicalNonPromotingEmpiricalContactReceipt
    ResidualPhaseObservableContactGeometry
    ResidualPhaseContactHamiltonian
    canonicalSourceBinding
    canonicalReplayArtifact

binarySplitObservableRecorded : Bool
binarySplitObservableRecorded = true

branchDepthObservableRecorded : Bool
branchDepthObservableRecorded = true

transitionPatternRecorded : Bool
transitionPatternRecorded = true

residualMismatchRecorded : Bool
residualMismatchRecorded = true

privateLexemeBoundaryRecorded : Bool
privateLexemeBoundaryRecorded = true

fibreRestrictionDoesNotRecoverCarrier : Bool
fibreRestrictionDoesNotRecoverCarrier = true

fibreRestrictionPromotesTruth : Bool
fibreRestrictionPromotesTruth = false

fixationMarkerRecorded : Bool
fixationMarkerRecorded = true

symbolicRecurrencePromotesTruth : Bool
symbolicRecurrencePromotesTruth = false

chaosBridgePromotesEmpiricalClaim : Bool
chaosBridgePromotesEmpiricalClaim = false

primorialBridgePromotesEmpiricalClaim : Bool
primorialBridgePromotesEmpiricalClaim = false

nonaryTonePromotesAuthority : Bool
nonaryTonePromotesAuthority = false

clinicalOrMetaphysicalClaimPromoted : Bool
clinicalOrMetaphysicalClaimPromoted = false

observableContactClosedProof :
  Receipt.observableContactClosed canonicalEmpiricalContactReceipt ≡ true
observableContactClosedProof =
  Receipt.canonicalObservableContactClosed
    ResidualPhaseObservableContactGeometry
    ResidualPhaseContactHamiltonian
    canonicalSourceBinding
    canonicalReplayArtifact

nonPromotionBoundaryClosedProof :
  Receipt.nonPromotionBoundaryClosed canonicalEmpiricalContactReceipt ≡ true
nonPromotionBoundaryClosedProof =
  Receipt.canonicalNonPromotionBoundaryClosed
    ResidualPhaseObservableContactGeometry
    ResidualPhaseContactHamiltonian
    canonicalSourceBinding
    canonicalReplayArtifact

empiricalAuthorityIsFalse :
  Receipt.authorityGateClosed canonicalEmpiricalContactReceipt ≡ false
empiricalAuthorityIsFalse = refl

promotesTruthIsFalse :
  Receipt.promotesTruth canonicalEmpiricalContactReceipt ≡ false
promotesTruthIsFalse = refl

fibreRestrictionTypedProof :
  Receipt.fibreRestrictionTyped canonicalEmpiricalContactReceipt ≡ true
fibreRestrictionTypedProof =
  Receipt.canonicalFibreRestrictionIsNonRecovering
    ResidualPhaseObservableContactGeometry
    refl
    ResidualPhaseContactHamiltonian
    canonicalSourceBinding
    canonicalReplayArtifact

------------------------------------------------------------------------
-- Canonical local witnesses
------------------------------------------------------------------------

canonicalPublicSplit : PublicSplit
canonicalPublicSplit = publicSplit "binary-split"

canonicalBranchStep : BranchStep
canonicalBranchStep = branchStep 1

canonicalBranchDepth : BranchDepth
canonicalBranchDepth = branchDepth 2

canonicalTraceEvent₀ : TraceEvent
canonicalTraceEvent₀ = traceEvent 0 "split-observed"

canonicalTraceEvent₁ : TraceEvent
canonicalTraceEvent₁ = traceEvent 1 "transition-observed"

canonicalPublicLabel : PublicLabel
canonicalPublicLabel = publicLabel "residual-mismatch"

canonicalLeftContext : LocalContext
canonicalLeftContext = localContext "pre-transition"

canonicalRightContext : LocalContext
canonicalRightContext = localContext "post-transition"

canonicalFixationMarker : FixationMarker
canonicalFixationMarker = fixationMarker "overheating-marker"

publicSplitObservableWitness :
  PublicSplitIsObservable canonicalPublicSplit
publicSplitObservableWitness = witness

branchDepthDyadicContactWitness :
  BranchDepthIsDyadicContact canonicalBranchStep canonicalBranchDepth
branchDepthDyadicContactWitness = witness

residualMismatchFibreEvidenceWitness :
  ResidualMismatchIsFibreEvidence
    canonicalPublicLabel
    canonicalLeftContext
    canonicalRightContext
residualMismatchFibreEvidenceWitness = witness

transitionPatternTemporalContactWitness :
  TransitionPatternIsTemporalContact
    canonicalTraceEvent₀
    canonicalTraceEvent₁
    branchingTransition
transitionPatternTemporalContactWitness = witness

fixationMarkerBlocksAuthorityWitness :
  AuthorityPromotionBlocked.empiricalAuthorityBlocked
    (FixationMarkerBlocksAuthority canonicalFixationMarker)
    ≡ false
fixationMarkerBlocksAuthorityWitness = refl
