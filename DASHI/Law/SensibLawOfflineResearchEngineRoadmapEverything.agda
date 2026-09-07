module DASHI.Law.SensibLawOfflineResearchEngineRoadmapEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawMultiResidualProofFrontierExact as Frontier
import DASHI.Law.SensibLawParsedAuthorityReasoningGraphExact as Reasoning
import DASHI.Law.SensibLawImmutableLegalResearchWorldExact as World
import DASHI.Law.SensibLawProofSearchIterationReceiptABIExact as Receipt
import DASHI.Law.SensibLawResearchCompoundingLoopExact as Compounding
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawProofSearchParetoSaturationExact as Pareto
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network

------------------------------------------------------------------------
-- OFFLINE RESEARCH ENGINE ROADMAP CAPSTONE
--
-- ProofFrontier
--   -> candidate support/defeater/comparator/contradiction moves
--   -> proof-reduction threshold + Pareto schedule
--   -> provider-neutral query
--   -> local/persisted execution first
--   -> PNF + proposition-level citation/reasoning/condition extraction
--   -> append-only world/research memory
--   -> frontier delta
--   -> next search
--
-- Governed live legal access remains a separately authorised strategy.
------------------------------------------------------------------------

record OfflineResearchEngineBoundary : Set where
  constructor offlineResearchEngineBoundary
  field
    frontierIsMultiResidual : Bool
    frontierIsMultiResidualIsTrue : frontierIsMultiResidual ≡ true
    parsedCasesEnrichReasoningGraph : Bool
    parsedCasesEnrichReasoningGraphIsTrue : parsedCasesEnrichReasoningGraph ≡ true
    conditionsCircumstancesAndTreatmentRetained : Bool
    conditionsCircumstancesAndTreatmentRetainedIsTrue :
      conditionsCircumstancesAndTreatmentRetained ≡ true
    researchMemoryIsAppendOnly : Bool
    researchMemoryIsAppendOnlyIsTrue : researchMemoryIsAppendOnly ≡ true
    runtimeIterationsHaveDeterministicReceiptABI : Bool
    runtimeIterationsHaveDeterministicReceiptABIIsTrue :
      runtimeIterationsHaveDeterministicReceiptABI ≡ true
    parsedResultsMayImproveNextSearch : Bool
    parsedResultsMayImproveNextSearchIsTrue : parsedResultsMayImproveNextSearch ≡ true
    liveNetworkExecutionImplicit : Bool
    liveNetworkExecutionImplicitIsFalse : liveNetworkExecutionImplicit ≡ false
    accumulatedResearchAutomaticallyTruth : Bool
    accumulatedResearchAutomaticallyTruthIsFalse : accumulatedResearchAutomaticallyTruth ≡ false

canonicalOfflineResearchEngineBoundary : OfflineResearchEngineBoundary
canonicalOfflineResearchEngineBoundary =
  offlineResearchEngineBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

selectedFrontierBoundary : Frontier.MultiResidualFrontierBoundary
selectedFrontierBoundary = Frontier.canonicalMultiResidualFrontierBoundary

selectedReasoningBoundary : Reasoning.ParsedAuthorityReasoningBoundary
selectedReasoningBoundary = Reasoning.canonicalParsedAuthorityReasoningBoundary

selectedWorldBoundary : World.ImmutableResearchWorldBoundary
selectedWorldBoundary = World.canonicalImmutableResearchWorldBoundary

selectedReceiptBoundary : Receipt.IterationReceiptABIBoundary
selectedReceiptBoundary = Receipt.canonicalIterationReceiptABIBoundary

selectedCompoundingBoundary : Compounding.ResearchCompoundingBoundary
selectedCompoundingBoundary = Compounding.canonicalResearchCompoundingBoundary

selectedQueryBoundary : Query.QueryAlgebraBoundary
selectedQueryBoundary = Query.canonicalQueryAlgebraBoundary

selectedParetoBoundary : Pareto.SearchParetoRefinementBoundary
selectedParetoBoundary = Pareto.canonicalSearchParetoRefinementBoundary

selectedNetworkBoundary : Network.GovernedLegalNetworkBoundary
selectedNetworkBoundary = Network.canonicalGovernedLegalNetworkBoundary

------------------------------------------------------------------------
-- Capstone firewalls.
------------------------------------------------------------------------

data MoreParsedCasesAutomaticallyCloseProof : Set where
data CitationGraphAutomaticallyCurrentAuthority : Set where
data ConditionsAutomaticallyApplicability : Set where
data ResearchMemoryAutomaticallyMonotoneConclusion : Set where
data RuntimeReceiptAutomaticallyAgdaProof : Set where

moreParsedCasesDoNotAutomaticallyCloseProof :
  MoreParsedCasesAutomaticallyCloseProof → ⊥
moreParsedCasesDoNotAutomaticallyCloseProof ()

citationGraphDoesNotAutomaticallyBecomeCurrentAuthority :
  CitationGraphAutomaticallyCurrentAuthority → ⊥
citationGraphDoesNotAutomaticallyBecomeCurrentAuthority ()

conditionsDoNotAutomaticallyBecomeApplicability :
  ConditionsAutomaticallyApplicability → ⊥
conditionsDoNotAutomaticallyBecomeApplicability ()

researchMemoryDoesNotForceMonotoneConclusion :
  ResearchMemoryAutomaticallyMonotoneConclusion → ⊥
researchMemoryDoesNotForceMonotoneConclusion ()

runtimeReceiptDoesNotBecomeAgdaProof : RuntimeReceiptAutomaticallyAgdaProof → ⊥
runtimeReceiptDoesNotBecomeAgdaProof ()
