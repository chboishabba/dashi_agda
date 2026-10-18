module DASHI.Core.GovernanceTrajectoryRealisationExact where

------------------------------------------------------------------------
-- Governance trajectory / realised-policy gap kernel.
--
-- This is the formal core recovered from the March 2026 O/R/C/S/L/P/G/F
-- governance discussion. It is deliberately party-neutral: concrete political
-- organisations, policies and historical claims enter only as source-indexed
-- witnesses supplied by downstream modules.
--
-- Prior-art welds:
--   * ContextIndexedPNFComparisonTransportExact: consumer/context scoping,
--     provenance, separate support/counter/missing coordinates.
--   * ContextualDialecticRoleExact: roles are frame-relative, not intrinsic.
--   * TernaryComparisonSynthesisExact: a later action/synthesis coordinate does
--     not erase the comparison that produced it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ContextIndexedPNFComparisonTransportExact as PNF
import DASHI.Core.ContextualDialecticRoleExact as Dialectic
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

------------------------------------------------------------------------
-- O / R / C / S / L / P / G / F carrier.
------------------------------------------------------------------------

record ZKPGovernanceModel
    (Organization Requirement Code State Lattice Proposal Gap : Set) : Set₁ where
  constructor zkp-governance-model
  field
    O : Organization
    R : Requirement
    C : Code
    S : State
    L : Lattice
    P : Proposal
    G : Proposal → State → Bool
    F : Organization → Requirement → Code → State → Lattice → Gap

open ZKPGovernanceModel public

record GovernanceDynamics
    (Organization Requirement Code State Lattice Proposal Gap : Set)
    (model : ZKPGovernanceModel Organization Requirement Code State Lattice Proposal Gap)
    : Set₁ where
  constructor governance-dynamics
  field
    transition :
      Organization → State → Proposal → Code → State
    latticeUpdate :
      Organization → Lattice → Proposal → Code → State → Lattice

open GovernanceDynamics public

stepState :
  ∀ {O R C S L P F}
    {m : ZKPGovernanceModel O R C S L P F} →
  GovernanceDynamics O R C S L P F m →
  O → S → P → C → S
stepState d = transition d

stepLattice :
  ∀ {O R C S L P F}
    {m : ZKPGovernanceModel O R C S L P F} →
  GovernanceDynamics O R C S L P F m →
  O → L → P → C → S → L
stepLattice d = latticeUpdate d

------------------------------------------------------------------------
-- Policy quality is not an intrinsic sign. It is indexed by context/frame.
------------------------------------------------------------------------

data ProposalOrientation : Set where
  supports neutral counters : ProposalOrientation

record ContextualProposalSystem (Frame Proposal : Set) : Set₁ where
  constructor contextual-proposal-system
  field
    orientationIn : Frame → Proposal → ProposalOrientation

open ContextualProposalSystem public

record ProposalOrientationChange
    {Frame Proposal : Set}
    (system : ContextualProposalSystem Frame Proposal) : Set where
  constructor proposal-orientation-change
  field
    proposal : Proposal
    firstFrame secondFrame : Frame
    orientationChanged :
      orientationIn system firstFrame proposal ≡
      orientationIn system secondFrame proposal → ⊥

open ProposalOrientationChange public

orientationChangeBlocksIntrinsicSign :
  ∀ {Frame Proposal}
    {system : ContextualProposalSystem Frame Proposal} →
  ProposalOrientationChange system →
  (intrinsic : Proposal → ProposalOrientation) →
  ((frame : Frame) (proposal : Proposal) →
    orientationIn system frame proposal ≡ intrinsic proposal) →
  ⊥
orientationChangeBlocksIntrinsicSign witness intrinsic agrees =
  orientationChanged witness
    (PNF.transEq
      (agrees (firstFrame witness) (proposal witness))
      (PNF.symEq (agrees (secondFrame witness) (proposal witness))))

------------------------------------------------------------------------
-- Incremental and threshold acceptance are distinct governance rules.
-- Neither is globally preferred by the kernel.
------------------------------------------------------------------------

record IncrementalAcceptance (State Proposal : Set) : Set₁ where
  constructor incremental-acceptance
  field
    improvesCurrentGap : State → Proposal → Set
    expandsFutureReachability : State → Proposal → Set
    acceptIncremental :
      (s : State) (p : Proposal) →
      improvesCurrentGap s p →
      expandsFutureReachability s p →
      Set

open IncrementalAcceptance public

record ThresholdAcceptance (State Proposal : Set) : Set₁ where
  constructor threshold-acceptance
  field
    clearsThreshold : State → Proposal → Set
    acceptableLockInRisk : State → Proposal → Set
    acceptThreshold :
      (s : State) (p : Proposal) →
      clearsThreshold s p →
      acceptableLockInRisk s p →
      Set

open ThresholdAcceptance public

record StrategyWitness
    {State Proposal : Set}
    (incremental : IncrementalAcceptance State Proposal)
    (threshold : ThresholdAcceptance State Proposal)
    (state : State)
    (proposal : Proposal) : Set₁ where
  constructor strategy-witness
  field
    incrementalPremise :
      improvesCurrentGap incremental state proposal
    reachabilityPremise :
      expandsFutureReachability incremental state proposal
    thresholdPremise :
      clearsThreshold threshold state proposal
    lockInPremise :
      acceptableLockInRisk threshold state proposal

open StrategyWitness public

------------------------------------------------------------------------
-- Evidence type and uncertainty remain explicit.
------------------------------------------------------------------------

data EvidenceKind : Set where
  observed interpolated counterfactual speculative : EvidenceKind

record GovernanceEvidence : Set where
  constructor governance-evidence
  field
    sourceRevision : String
    statementRef : String
    provenanceRefs : List String
    kind : EvidenceKind
    supportRefs : List String
    counterRefs : List String
    missingRefs : List String

open GovernanceEvidence public

record GapEstimate (Gap Uncertainty : Set) : Set₁ where
  constructor gap-estimate
  field
    gap : Gap
    uncertainty : Uncertainty
    evidence : List GovernanceEvidence

open GapEstimate public

------------------------------------------------------------------------
-- A comparative claim is witness-scoped. The kernel does not manufacture a
-- universal ranking from one historical trace.
------------------------------------------------------------------------

record ComparativeWitness
    (Organization Requirement Code State Lattice Gap Uncertainty : Set)
    (gapFn : Organization → Requirement → Code → State → Lattice → Gap)
    : Set₁ where
  constructor comparative-witness
  field
    left right : Organization
    requirement : Requirement
    code : Code
    state : State
    lattice : Lattice
    leftEstimate rightEstimate : GapEstimate Gap Uncertainty
    leftEstimateMatches :
      gap leftEstimate ≡ gapFn left requirement code state lattice
    rightEstimateMatches :
      gap rightEstimate ≡ gapFn right requirement code state lattice
    sourceFrame : PNF.ConsumerFrame

open ComparativeWitness public

record LocalGapOrdering {Gap : Set} (left right : Gap) : Set₁ where
  constructor local-gap-ordering
  field
    leftBetterThanRight : Set
    witnessRef : String

open LocalGapOrdering public

record ScopedComparativeClaim
    {Organization Requirement Code State Lattice Gap Uncertainty : Set}
    {gapFn : Organization → Requirement → Code → State → Lattice → Gap}
    (w : ComparativeWitness Organization Requirement Code State Lattice Gap Uncertainty gapFn)
    : Set₁ where
  constructor scoped-comparative-claim
  field
    ordering :
      LocalGapOrdering (gap (leftEstimate w)) (gap (rightEstimate w))
    reviewRequired : Bool
    universalDominanceClaimed : Bool
    universalDominanceClaimedIsFalse :
      universalDominanceClaimed ≡ false

open ScopedComparativeClaim public

------------------------------------------------------------------------
-- Ternary/dialectic cross-pollination boundaries.
------------------------------------------------------------------------

existingRolesAreContextual :
  Dialectic.roleMayChangeWithComparisonFrame
    Dialectic.canonicalContextualDialecticRoleBoundary ≡ true
existingRolesAreContextual = refl

existingSynthesisRetainsComparison :
  Synthesis.synthesisErasesComparisonBoundary
    Synthesis.canonicalTernaryComparisonSynthesisBoundary ≡ false
existingSynthesisRetainsComparison = refl

------------------------------------------------------------------------
-- Concrete non-political fixture: the same proposal can support one frame and
-- counter another. This proves contextuality without encoding a party verdict.
------------------------------------------------------------------------

data DemoFrame : Set where
  immediateOutcome futureReachability : DemoFrame

data DemoProposal : Set where
  sameProposal : DemoProposal

demoProposalSystem : ContextualProposalSystem DemoFrame DemoProposal
demoProposalSystem = contextual-proposal-system assess
  where
    assess : DemoFrame → DemoProposal → ProposalOrientation
    assess immediateOutcome sameProposal = supports
    assess futureReachability sameProposal = counters

demoOrientationChanges : ProposalOrientationChange demoProposalSystem
demoOrientationChanges =
  proposal-orientation-change
    sameProposal
    immediateOutcome
    futureReachability
    (λ ())

noIntrinsicProposalSign :
  (intrinsic : DemoProposal → ProposalOrientation) →
  ((frame : DemoFrame) (proposal : DemoProposal) →
    orientationIn demoProposalSystem frame proposal ≡ intrinsic proposal) →
  ⊥
noIntrinsicProposalSign =
  orientationChangeBlocksIntrinsicSign demoOrientationChanges

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record GovernanceTrajectoryBoundary : Set where
  constructor governance-trajectory-boundary
  field
    contextIndexedProposalSign : Bool
    contextIndexedProposalSignIsTrue : contextIndexedProposalSign ≡ true
    thresholdAndIncrementalSeparated : Bool
    thresholdAndIncrementalSeparatedIsTrue :
      thresholdAndIncrementalSeparated ≡ true
    evidenceKindTracked : Bool
    evidenceKindTrackedIsTrue : evidenceKindTracked ≡ true
    historicalWitnessImpliesUniversalRanking : Bool
    historicalWitnessImpliesUniversalRankingIsFalse :
      historicalWitnessImpliesUniversalRanking ≡ false
    synthesisErasesPriorComparison : Bool
    synthesisErasesPriorComparisonIsFalse :
      synthesisErasesPriorComparison ≡ false

canonicalGovernanceTrajectoryBoundary : GovernanceTrajectoryBoundary
canonicalGovernanceTrajectoryBoundary =
  governance-trajectory-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
