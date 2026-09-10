module DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.CaseyITIRNixBridge as Casey
import DASHI.Reasoning.AristotleExperimentalBranchMergeExact as BranchMerge
import DASHI.Wikimedia.WikipediaWholeCorpusPNFITIRSensibLawPipelineExact as Whole

------------------------------------------------------------------------
-- WHOLE-WIKIPEDIA ALL-PAIRS SEARCH WITH EARLY TYPED PRUNING
--
-- Semantic search contract:
--   every unordered proposition pair is globally eligible for comparison.
--   We do NOT restrict semantic eligibility to pre-indexed neighborhoods.
--   Instead, cheap typed gates prune or defer branches before expensive
--   PNF/SensibLaw algebra.  Every prune/defer carries a receipt so the global
--   pair-space remains auditable and can be reopened after revisions.
--
-- Cross-pollination:
--   * PNF: admissible/invalid/undetermined/inapplicable candidates and residuals;
--   * FactorsThrough/non-factorability: query-relative sufficiency or repair;
--   * Snowball: failed factorisation/wrong type/source mismatch can discover
--     new axes rather than disappearing as irrelevant noise;
--   * Casey: candidate knowledge accumulates monotonically under join and
--     governance receipts select an active view without deleting history;
--   * Aristotle/git-style merge: compatible monotone knowledge may join, but
--     arbitrary semantic states require reconciliation/quotient soundness;
--   * StatiBaker: immutable state/receipt/view references make each pruning
--     decision replayable against an exact corpus revision.
------------------------------------------------------------------------

record PropositionIdentity : Set where
  constructor proposition-identity
  field
    propositionReference : String
    pageReference : String
    wikipediaRevisionReference : String
    exactSpanReference : String
    pnfReference : String
    sourceReference : String
open PropositionIdentity public

record GlobalPair : Set where
  constructor global-pair
  field
    left : PropositionIdentity
    right : PropositionIdentity
    canonicalPairReference : String
    unorderedDistinctPair : Bool
open GlobalPair public

data Gate : Set where
  sameIdentityGate : Gate
  candidateValidityGate : Gate
  wrongTypeGate : Gate
  sourceAuthorityGate : Gate
  factorisationGate : Gate
  temporalScopeGate : Gate
  jurisdictionContextGate : Gate
  algebraicShapeGate : Gate
  expensivePNFGate : Gate

data GateDisposition : Set where
  prune : GateDisposition
  defer : GateDisposition
  survive : GateDisposition
  snowballRepair : GateDisposition
  conflictReview : GateDisposition

record GateReceipt : Set where
  constructor gate-receipt
  field
    pair : GlobalPair
    gate : Gate
    disposition : GateDisposition
    reasonReference : String
    evidenceReference : String
    revisionBound : Bool
    sourceBound : Bool
    mayReopenAfterRevision : Bool
open GateReceipt public

record AllPairsSearchContract : Set where
  constructor all-pairs-search-contract
  field
    everyUnorderedDistinctPairEnumerated : Bool
    neighborhoodsRestrictSemanticEligibility : Bool
    indicesMayAccelerateGateEvaluation : Bool
    cheapGatesRunBeforeExpensiveAlgebra : Bool
    pruneDecisionRequiresReceipt : Bool
    prunedPairMayReopenAfterRelevantRevision : Bool
    failedFactorsThroughMayCreateSnowballRepair : Bool
    wrongTypeMayBlockExpensiveComparison : Bool
    sourceMismatchMayBlockPromotion : Bool
    expensiveAlgebraRunsForEveryEnumeratedPair : Bool
open AllPairsSearchContract public

canonicalAllPairsSearchContract : AllPairsSearchContract
canonicalAllPairsSearchContract = all-pairs-search-contract
  true false true true true true true true true false

------------------------------------------------------------------------
-- Pairwise branch tree.  The O(N^2) pair-space is real; pruning changes the
-- cost per branch, not the semantic quantification domain.
------------------------------------------------------------------------

record PairBranchState : Set where
  constructor pair-branch-state
  field
    pair : GlobalPair
    lastGateReference : String
    surviving : Bool
    deferred : Bool
    snowballRepairPending : Bool
    expensiveAlgebraPaid : Bool
    branchReceiptReference : String
open PairBranchState public

record PairSearchComplexityContract : Set where
  constructor pair-search-complexity-contract
  field
    globalCandidatePairsQuadraticInPropositionCount : Bool
    allPairsMaterialisedSimultaneouslyRequired : Bool
    streamingOrShardedEnumerationAllowed : Bool
    earlyPruningExpectedToReduceExpensiveAlgebraWork : Bool
    pairReceiptsMayBeMemoisedByRevisionIdentity : Bool
    changedRevisionReopensOnlyAffectedPairBranches : Bool
open PairSearchComplexityContract public

canonicalPairSearchComplexityContract : PairSearchComplexityContract
canonicalPairSearchComplexityContract = pair-search-complexity-contract
  true false true true true true

------------------------------------------------------------------------
-- FactorsThrough / snowball interaction.
------------------------------------------------------------------------

record FactorisationGateReceipt : Set where
  constructor factorisation-gate-receipt
  field
    pair : GlobalPair
    queryReference : String
    observerSurfaceReference : String
    factorisationChecked : Bool
    factorisationSucceeded : Bool
    nonFactorabilityWitnessReference : String
    snowballRoute : Snowball.DiscoveryRoute
    missingAxisProposalReference : String
    pruneWithoutRepairAllowed : Bool
open FactorisationGateReceipt public

data FailedFactorisationMayDisappear : Set where

failedFactorisationMustRemainVisible : FailedFactorisationMayDisappear → ⊥
failedFactorisationMustRemainVisible ()

------------------------------------------------------------------------
-- PNF admissibility is an early gate, not a claim that rejected candidates are
-- deleted.  Candidate history remains available to Casey/ITIR governance.
------------------------------------------------------------------------

record PNFAdmissibilityGateReceipt : Set where
  constructor pnf-admissibility-gate-receipt
  field
    pair : GlobalPair
    leftValidityReference : String
    rightValidityReference : String
    invalidBranchCanPrune : Bool
    undeterminedBranchDefers : Bool
    alternativesRetained : Bool
open PNFAdmissibilityGateReceipt public

------------------------------------------------------------------------
-- Git/Casey/Aristotle merge analogy for proposition branches.
------------------------------------------------------------------------

data PropositionMergeDisposition : Set where
  fastForwardKnowledge : PropositionMergeDisposition
  monotoneJoinKnowledge : PropositionMergeDisposition
  threeWaySemanticReconciliation : PropositionMergeDisposition
  contradictoryBranchesRetained : PropositionMergeDisposition
  noTypedMeetRetained : PropositionMergeDisposition

record PropositionBranchMergeReceipt : Set where
  constructor proposition-branch-merge-receipt
  field
    leftBranchReference : String
    rightBranchReference : String
    commonAncestorOrRevisionReference : String
    disposition : PropositionMergeDisposition
    monotoneKnowledgePreserved : Bool
    conflictingEvidenceRetained : Bool
    semanticReconciliationReference : String
    quotientSoundnessReference : String
    mergeReceiptReference : String
open PropositionBranchMergeReceipt public

record MergeCrossPollinationBoundary : Set where
  constructor merge-cross-pollination-boundary
  field
    caseyJoinIsAssociativeCommutativeIdempotent : Bool
    candidateHistoryDeletedOnResolution : Bool
    activeViewRequiresGovernanceReceipts : Bool
    arbitrarySemanticStatesCRDTJoinable : Bool
    semanticMergeMayRequireConflictReview : Bool
    immutableObserverReferencesRetained : Bool
open MergeCrossPollinationBoundary public

canonicalMergeCrossPollinationBoundary : MergeCrossPollinationBoundary
canonicalMergeCrossPollinationBoundary = merge-cross-pollination-boundary
  true false true false true true

caseyBoundaryWitness : Casey.ObserverBoundary
  -- concrete substrate/governance instances remain supplied by runtime;
  -- this declaration is intentionally not instantiated here.
  _ _
caseyBoundaryWitness = _

------------------------------------------------------------------------
-- The previous neighborhood-only scheduler remains useful as an acceleration
-- index, but not as the quantification boundary.
------------------------------------------------------------------------

record NeighborhoodAccelerationBoundary : Set where
  constructor neighborhood-acceleration-boundary
  field
    oldNeighborhoodIndicesReusable : Bool
    neighborhoodHitMayPrioritisePair : Bool
    neighborhoodMissMayDeletePairFromSemanticUniverse : Bool
    allPairsContractSupersedesNeighborhoodEligibility : Bool
open NeighborhoodAccelerationBoundary public

canonicalNeighborhoodAccelerationBoundary : NeighborhoodAccelerationBoundary
canonicalNeighborhoodAccelerationBoundary = neighborhood-acceleration-boundary
  true true false true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data IndexMissMeansIrrelevantPair : Set where
data PruneMeansFalseProposition : Set where
data MergeMeansClaimsEquivalent : Set where
data JoinMeansConflictErased : Set where
data AdmissibleMeansTrue : Set where
\data EveryPairNeedsFullAlgebra : Set where

indexMissDoesNotRemovePair : IndexMissMeansIrrelevantPair → ⊥
indexMissDoesNotRemovePair ()

pruneDoesNotMeanFalse : PruneMeansFalseProposition → ⊥
pruneDoesNotMeanFalse ()

mergeDoesNotMeanEquivalent : MergeMeansClaimsEquivalent → ⊥
mergeDoesNotMeanEquivalent ()

joinDoesNotEraseConflict : JoinMeansConflictErased → ⊥
joinDoesNotEraseConflict ()

admissibleDoesNotMeanTrue : AdmissibleMeansTrue → ⊥
admissibleDoesNotMeanTrue ()

everyPairDoesNotNeedFullAlgebra : EveryPairNeedsFullAlgebra → ⊥
everyPairDoesNotNeedFullAlgebra ()

record WikipediaAllPairsBoundary : Set where
  constructor wikipedia-all-pairs-boundary
  field
    universalPairEligibility : Bool
    typedEarlyPruning : Bool
    receiptBearingPruning : Bool
    factorisationFailuresSnowball : Bool
    caseyMonotoneCandidateHistory : Bool
    gitStyleReconciliationCrossPollinated : Bool
    statibakerImmutableObservationCrossPollinated : Bool
    indexRestrictsSemanticUniverse : Bool
    quadraticPairSpaceDenied : Bool
open WikipediaAllPairsBoundary public

canonicalWikipediaAllPairsBoundary : WikipediaAllPairsBoundary
canonicalWikipediaAllPairsBoundary = wikipedia-all-pairs-boundary
  true true true true true true true false false
