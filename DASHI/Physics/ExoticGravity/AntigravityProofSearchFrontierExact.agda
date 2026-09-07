module DASHI.Physics.ExoticGravity.AntigravityProofSearchFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentSearchHypergraphExact as Hyper
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Unified
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- ANTIGRAVITY PROOF-SEARCH FRONTIER
--
-- This owner does not add a second search engine.  It reads the exact current
-- superconducting-gravity evidence state through the existing evidence owner,
-- refines its first open leaf into the existing hypergraph dependencies, and
-- declares only the information moves needed along that reachable cut.
------------------------------------------------------------------------

data AntigravitySearchResidual : Set where
  sourceCharacterisationResidual : AntigravitySearchResidual
  transitionLockResidual : AntigravitySearchResidual
  backgroundClosureResidual : AntigravitySearchResidual
  constitutiveResidual : AntigravitySearchResidual
  theoryComparisonResidual : AntigravitySearchResidual

residualForEvidenceLeaf : Evidence.EvidenceLeaf → AntigravitySearchResidual
residualForEvidenceLeaf Evidence.sourceCharacterisationLeaf = sourceCharacterisationResidual
residualForEvidenceLeaf Evidence.transitionLockLeaf = transitionLockResidual
residualForEvidenceLeaf Evidence.externalProbeLeaf = theoryComparisonResidual
residualForEvidenceLeaf Evidence.backgroundClosureLeaf = backgroundClosureResidual
residualForEvidenceLeaf Evidence.replicationLeaf = theoryComparisonResidual
residualForEvidenceLeaf Evidence.constitutiveResidualLeaf = constitutiveResidual
residualForEvidenceLeaf Evidence.boundedNoPromotionLeaf = theoryComparisonResidual

------------------------------------------------------------------------
-- Exact current public-literature frontier.
------------------------------------------------------------------------

currentEvidenceLeafIsSourceCharacterisation :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.sourceCharacterisationLeaf
currentEvidenceLeafIsSourceCharacterisation = refl

currentAntigravityResidual : AntigravitySearchResidual
currentAntigravityResidual = residualForEvidenceLeaf Evidence.currentFirstOpenEvidenceLeaf

currentResidualIsSourceCharacterisation :
  currentAntigravityResidual ≡ sourceCharacterisationResidual
currentResidualIsSourceCharacterisation = refl

------------------------------------------------------------------------
-- The coarse source-characterisation evidence leaf refines to an AND-cut in
-- the existing hypergraph: source current plus source stress-energy.
------------------------------------------------------------------------

sourceCharacterisationHypergraphCut : List Hyper.SearchState
sourceCharacterisationHypergraphCut =
  Hyper.sourceCurrentLeaf ∷ Hyper.sourceStressEnergyLeaf ∷ []

record CurrentSourceCharacterisationDemand : Set where
  constructor current-source-characterisation-demand
  field
    currentResidual : AntigravitySearchResidual
    currentResidualMatches : currentResidual ≡ currentAntigravityResidual
    requiredHypergraphLeaves : List Hyper.SearchState
    requiredHypergraphLeavesMatch :
      requiredHypergraphLeaves ≡ sourceCharacterisationHypergraphCut
    selectedMove : Choice.InformationMove
    selectedMoveMatches : selectedMove ≡ Hyper.characteriseSourceMove

open CurrentSourceCharacterisationDemand public

canonicalCurrentSourceCharacterisationDemand : CurrentSourceCharacterisationDemand
canonicalCurrentSourceCharacterisationDemand =
  current-source-characterisation-demand
    sourceCharacterisationResidual refl
    sourceCharacterisationHypergraphCut refl
    Hyper.characteriseSourceMove refl

------------------------------------------------------------------------
-- Introspective skip proofs: external-probe ownership and replication are
-- already true in the current evidence carrier, so neither may be scheduled as
-- the first live leaf merely because they are scientifically interesting.
------------------------------------------------------------------------

externalProbeIsNotCurrentFirstOpenLeaf :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.externalProbeLeaf → ⊥
externalProbeIsNotCurrentFirstOpenLeaf ()

replicationIsNotCurrentFirstOpenLeaf :
  Evidence.currentFirstOpenEvidenceLeaf ≡ Evidence.replicationLeaf → ⊥
replicationIsNotCurrentFirstOpenLeaf ()

------------------------------------------------------------------------
-- Counterfactual frontier recomputation after paying only the current leaf.
-- The already-owned external probe and replication are retained.  Therefore
-- the shortest reachable sequence skips them rather than paying them twice.
------------------------------------------------------------------------

afterSourceCharacterisation : Evidence.EvidenceClosureState
afterSourceCharacterisation =
  Evidence.evidence-closure-state true false true false true false

afterSourceFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterSourceCharacterisation
    ≡ Evidence.transitionLockLeaf
afterSourceFirstOpen = refl

afterTransitionLock : Evidence.EvidenceClosureState
afterTransitionLock =
  Evidence.evidence-closure-state true true true false true false

afterTransitionFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterTransitionLock
    ≡ Evidence.backgroundClosureLeaf
afterTransitionFirstOpen = refl

afterBackgroundClosure : Evidence.EvidenceClosureState
afterBackgroundClosure =
  Evidence.evidence-closure-state true true true true true false

afterBackgroundFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterBackgroundClosure
    ≡ Evidence.constitutiveResidualLeaf
afterBackgroundFirstOpen = refl

afterConstitutiveResidual : Evidence.EvidenceClosureState
afterConstitutiveResidual =
  Evidence.evidence-closure-state true true true true true true

afterConstitutiveFirstOpen :
  Evidence.firstOpenEvidenceLeaf afterConstitutiveResidual
    ≡ Evidence.boundedNoPromotionLeaf
afterConstitutiveFirstOpen = refl

------------------------------------------------------------------------
-- Existing information moves for the first three reachable residuals.  The
-- final constitutive computation is a thin declared move because the generic
-- hypergraph has the leaf/action but no InformationMove wrapper for it.
------------------------------------------------------------------------

sourceCharacterisationMove : Choice.InformationMove
sourceCharacterisationMove = Hyper.characteriseSourceMove

transitionLockMove : Choice.InformationMove
transitionLockMove = Hyper.crossTcMove

backgroundClosureMove : Choice.InformationMove
backgroundClosureMove = Hyper.closeBackgroundMove

constitutiveResidualMove : Choice.InformationMove
constitutiveResidualMove = Choice.informationMove
  Choice.takeMeasurement 4
  "compute the same-apparatus source-normalised constitutive residual"
  "requires paid source-characterisation, transition-lock, external-probe, background-closure and replication receipts"
  "consumer-bound constitutive-residual calculation on the exact completed apparatus state"

shortestReachableDeclaredMoves : List Choice.InformationMove
shortestReachableDeclaredMoves =
  sourceCharacterisationMove ∷
  transitionLockMove ∷
  backgroundClosureMove ∷
  constitutiveResidualMove ∷ []

------------------------------------------------------------------------
-- Completing the experimental/evidence cut does not yield antigravity.  It
-- reaches the theory-comparison consumer, where an attributed ordinary-GR
-- prediction and a competing prediction must be welded to the same observation.
------------------------------------------------------------------------

postEvidenceRoute : Unified.ClaimObservationRoute → AntigravitySearchResidual
postEvidenceRoute (Unified.gravitationalObservationRoute channel) = theoryComparisonResidual
postEvidenceRoute Unified.inertialComparisonRoute = theoryComparisonResidual
postEvidenceRoute Unified.ordinaryMomentumClosureRoute = theoryComparisonResidual

record AntigravityProofSearchBoundary : Set where
  constructor antigravity-proof-search-boundary
  field
    currentFirstResidualIsSourceCharacterisation : Bool
    sourceCharacterisationIsSingleScalarLeaf : Bool
    alreadyOwnedExternalProbeMustBeReacquiredFirst : Bool
    alreadyOwnedReplicationMustBeReacquiredFirst : Bool
    shortestPathMaySkipAlreadyOwnedLeaves : Bool
    completedEvidenceCutAutomaticallyProvesAntigravity : Bool
    completedEvidenceCutReachesTheoryComparison : Bool
    rawExperimentalFindingAutomaticallyClosesKernelProof : Bool

canonicalAntigravityProofSearchBoundary : AntigravityProofSearchBoundary
canonicalAntigravityProofSearchBoundary =
  antigravity-proof-search-boundary
    true false false false true false true false

------------------------------------------------------------------------
-- Observation-channel fixtures remain typed at the consumer boundary.
------------------------------------------------------------------------

freeFallPostEvidenceResidual : AntigravitySearchResidual
freeFallPostEvidenceResidual =
  postEvidenceRoute
    (Unified.gravitationalObservationRoute Obs.freeFallEquivalence)

remoteFieldPostEvidenceResidual : AntigravitySearchResidual
remoteFieldPostEvidenceResidual =
  postEvidenceRoute
    (Unified.gravitationalObservationRoute Obs.localTestMassAcceleration)

freeFallPostEvidenceNeedsTheoryComparison :
  freeFallPostEvidenceResidual ≡ theoryComparisonResidual
freeFallPostEvidenceNeedsTheoryComparison = refl

remoteFieldPostEvidenceNeedsTheoryComparison :
  remoteFieldPostEvidenceResidual ≡ theoryComparisonResidual
remoteFieldPostEvidenceNeedsTheoryComparison = refl
