module DASHI.Law.SensibLawProofDirectedCorpusSearchEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawCitationAuthorityFollowExact as CitationFollow
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result
import DASHI.Law.SensibLawProofSearchParetoSaturationExact as Pareto
import DASHI.Law.SensibLawSearchExecutionCostParetoExact as ExecutionCost
import DASHI.Law.SensibLawCostedProofSearchSchedulerExact as CostScheduler
import DASHI.Law.SensibLawSparseWorldModelAcquisitionExact as World
import DASHI.Law.SensibLawPrecedentGeometryStatisticsExact as Geometry
import DASHI.Law.SensibLawProofSearchExpansionBidiExact as Expansion
import DASHI.Law.SensibLawBidirectionalWorldLawProofSearchExact as Bidi
import DASHI.Law.SensibLawWaterproofArgumentGapSearchExact as Waterproof
import DASHI.Law.SensibLawTextWitnessTransmissionProvenanceExact as Witness
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Law.SensibLawHistoricalLegalResearchOperatorExact as Historical
import DASHI.Law.SensibLawProofGapExecutableSearchCompilerExact as Compiler
import DASHI.Law.SensibLawIterativeProofSearchStateMachineExact as Iterative
import DASHI.Law.SensibLawMaboPabaiExecutableProofSearchExact as Fixture

------------------------------------------------------------------------
-- PROOF-DIRECTED CORPUS NAVIGATION CAPSTONE
--
-- consumer/question
--   -> proof cutset / smallest live gap
--   -> typed producer
--   -> search intent
--   -> support/defeater/comparator hypothesis family
--   -> provider-neutral query algebra
--   -> execution cost/value Pareto surface
--   -> provider lowering or citation traversal
--   -> bounded legal-follow / corpus acquisition
--   -> same parser / PNF re-entry with witness lineage retained
--   -> proposition/authority/treatment assessment
--   -> proof payment / frontier delta
--   -> costed iterative Pareto continuation or saturation
--   -> memoised world-model extension
------------------------------------------------------------------------

record ProofDirectedCorpusSearchContract : Set where
  constructor proofDirectedCorpusSearchContract
  field
    proofGapPrecedesQueryString : Bool
    proofGapPrecedesQueryStringIsTrue : proofGapPrecedesQueryString ≡ true

    producerPrecedesProvider : Bool
    producerPrecedesProviderIsTrue : producerPrecedesProvider ≡ true

    supportAndDefeaterSearchPaired : Bool
    supportAndDefeaterSearchPairedIsTrue : supportAndDefeaterSearchPaired ≡ true

    proximityIsCandidateGenerationOnly : Bool
    proximityIsCandidateGenerationOnlyIsTrue : proximityIsCandidateGenerationOnly ≡ true

    citationAcquisitionReentersPNF : Bool
    citationAcquisitionReentersPNFIsTrue : citationAcquisitionReentersPNF ≡ true

    transmissionWitnessLineageRetained : Bool
    transmissionWitnessLineageRetainedIsTrue : transmissionWitnessLineageRetained ≡ true

    legalFollowConstraintsSurviveCompilation : Bool
    legalFollowConstraintsSurviveCompilationIsTrue :
      legalFollowConstraintsSurviveCompilation ≡ true

    historicalSparseResearchAvailable : Bool
    historicalSparseResearchAvailableIsTrue : historicalSparseResearchAvailable ≡ true

    gapCompilesEndToEnd : Bool
    gapCompilesEndToEndIsTrue : gapCompilesEndToEnd ≡ true

    iterativeFrontierSearchOwned : Bool
    iterativeFrontierSearchOwnedIsTrue : iterativeFrontierSearchOwned ≡ true

    executionStrategyCostedSeparately : Bool
    executionStrategyCostedSeparatelyIsTrue : executionStrategyCostedSeparately ≡ true

    proofReductionThresholdPrecedesCostOptimisation : Bool
    proofReductionThresholdPrecedesCostOptimisationIsTrue :
      proofReductionThresholdPrecedesCostOptimisation ≡ true

    retrievalRequiresProofAssessment : Bool
    retrievalRequiresProofAssessmentIsTrue : retrievalRequiresProofAssessment ≡ true

    worldEvidenceAndLegalAuthoritySeparated : Bool
    worldEvidenceAndLegalAuthoritySeparatedIsTrue :
      worldEvidenceAndLegalAuthoritySeparated ≡ true

    parseBroadlyResolveSelectively : Bool
    parseBroadlyResolveSelectivelyIsTrue : parseBroadlyResolveSelectively ≡ true

    statisticsGuideButDoNotCreateDoctrine : Bool
    statisticsGuideButDoNotCreateDoctrineIsTrue :
      statisticsGuideButDoNotCreateDoctrine ≡ true

    saturationIsFrontierRelative : Bool
    saturationIsFrontierRelativeIsTrue : saturationIsFrontierRelative ≡ true

    maboAndPabaiAreSearchCalibrations : Bool
    maboAndPabaiAreSearchCalibrationsIsTrue : maboAndPabaiAreSearchCalibrations ≡ true

canonicalProofDirectedCorpusSearchContract : ProofDirectedCorpusSearchContract
canonicalProofDirectedCorpusSearchContract = proofDirectedCorpusSearchContract
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl
  true refl

------------------------------------------------------------------------
-- Pin canonical component boundaries.
------------------------------------------------------------------------

selectedIntentBoundary : Intent.ProofDirectedSearchBoundary
selectedIntentBoundary = Intent.canonicalProofDirectedSearchBoundary

selectedQueryBoundary : Query.QueryAlgebraBoundary
selectedQueryBoundary = Query.canonicalQueryAlgebraBoundary

selectedCitationFollowBoundary : CitationFollow.CitationFollowBoundary
selectedCitationFollowBoundary = CitationFollow.canonicalCitationFollowBoundary

selectedCitationUseBoundary : CitationUse.CitationUseBoundary
selectedCitationUseBoundary = CitationUse.canonicalCitationUseBoundary

selectedCorpusBoundary : Corpus.CorpusRoutingBoundary
selectedCorpusBoundary = Corpus.canonicalCorpusRoutingBoundary

selectedDialecticalBoundary : Dialectic.DialecticalSearchBoundary
selectedDialecticalBoundary = Dialectic.canonicalDialecticalSearchBoundary

selectedResultBoundary : Result.ResultAssessmentBoundary
selectedResultBoundary = Result.canonicalResultAssessmentBoundary

selectedParetoBoundary : Pareto.SearchParetoRefinementBoundary
selectedParetoBoundary = Pareto.canonicalSearchParetoRefinementBoundary

selectedExecutionCostBoundary : ExecutionCost.SearchExecutionCostBoundary
selectedExecutionCostBoundary = ExecutionCost.canonicalSearchExecutionCostBoundary

selectedCostSchedulerBoundary : CostScheduler.CostedProofSearchSchedulerBoundary
selectedCostSchedulerBoundary = CostScheduler.canonicalCostedProofSearchSchedulerBoundary

selectedSaturationBoundary : Pareto.SearchSaturationBoundary
selectedSaturationBoundary = Pareto.canonicalSearchSaturationBoundary

selectedWorldBoundary : World.SparseWorldBoundary
selectedWorldBoundary = World.canonicalSparseWorldBoundary

selectedGeometryBoundary : Geometry.PrecedentGeometryBoundary
selectedGeometryBoundary = Geometry.canonicalPrecedentGeometryBoundary

selectedExpansionBoundary : Expansion.ExpansionBoundary
selectedExpansionBoundary = Expansion.canonicalExpansionBoundary

selectedBidirectionalBoundary : Bidi.BidirectionalSearchBoundary
selectedBidirectionalBoundary = Bidi.canonicalBidirectionalSearchBoundary

selectedWaterproofBoundary : Waterproof.WaterproofArgumentBoundary
selectedWaterproofBoundary = Waterproof.canonicalWaterproofArgumentBoundary

selectedWitnessBoundary : Witness.TextWitnessBoundary
selectedWitnessBoundary = Witness.canonicalTextWitnessBoundary

selectedLegalFollowBoundary : LegalFollow.LegalFollowProofSearchBoundary
selectedLegalFollowBoundary = LegalFollow.canonicalLegalFollowProofSearchBoundary

selectedHistoricalBoundary : Historical.HistoricalResearchBoundary
selectedHistoricalBoundary = Historical.canonicalHistoricalResearchBoundary

selectedCompilerBoundary : Compiler.EndToEndSearchCompilerBoundary
selectedCompilerBoundary = Compiler.canonicalEndToEndSearchCompilerBoundary

selectedIterativeBoundary : Iterative.IterativeProofSearchBoundary
selectedIterativeBoundary = Iterative.canonicalIterativeProofSearchBoundary

selectedMaboPabaiBoundary : Fixture.MaboPabaiSearchBoundary
selectedMaboPabaiBoundary = Fixture.canonicalMaboPabaiSearchBoundary

------------------------------------------------------------------------
-- Canonical no-collapse laws.
------------------------------------------------------------------------

data SearchResultEqualsTruth : Set where
data SearchResultEqualsAuthority : Set where
data SearchResultEqualsApplicability : Set where
data SearchResultEqualsProofPayment : Set where
data WorldModelCompletenessRequiredBeforeUse : Set where
data MaboTopologyAutomaticallyTransfersToPabaiDoctrine : Set where
data StatisticalSeparatorAutomaticallyLegalRule : Set where
data MoreCasesAutomaticallyMakeArgumentWaterproof : Set where
data RepeatedPublicationAutomaticallyIndependentTruth : Set where
data HistoricalSparseSearchEqualsFinalWorldModel : Set where
data ExecutableQueryCompilerMayBypassAssessment : Set where
data CheapestExecutionAutomaticallyBestProofSearch : Set where

searchResultDoesNotEqualTruth : SearchResultEqualsTruth → ⊥
searchResultDoesNotEqualTruth ()

searchResultDoesNotEqualAuthority : SearchResultEqualsAuthority → ⊥
searchResultDoesNotEqualAuthority ()

searchResultDoesNotEqualApplicability : SearchResultEqualsApplicability → ⊥
searchResultDoesNotEqualApplicability ()

searchResultDoesNotEqualProofPayment : SearchResultEqualsProofPayment → ⊥
searchResultDoesNotEqualProofPayment ()

worldNeedNotBeCompleteBeforeUse : WorldModelCompletenessRequiredBeforeUse → ⊥
worldNeedNotBeCompleteBeforeUse ()

maboTopologyDoesNotTransferDoctrine : MaboTopologyAutomaticallyTransfersToPabaiDoctrine → ⊥
maboTopologyDoesNotTransferDoctrine ()

statisticalSeparatorDoesNotBecomeRule : StatisticalSeparatorAutomaticallyLegalRule → ⊥
statisticalSeparatorDoesNotBecomeRule ()

moreCasesDoNotAutomaticallyWaterproofArgument : MoreCasesAutomaticallyMakeArgumentWaterproof → ⊥
moreCasesDoNotAutomaticallyWaterproofArgument ()

repeatedPublicationDoesNotCreateIndependentTruth :
  RepeatedPublicationAutomaticallyIndependentTruth → ⊥
repeatedPublicationDoesNotCreateIndependentTruth ()

historicalSparseSearchDoesNotEqualFinalWorld :
  HistoricalSparseSearchEqualsFinalWorldModel → ⊥
historicalSparseSearchDoesNotEqualFinalWorld ()

queryCompilerDoesNotBypassAssessment :
  ExecutableQueryCompilerMayBypassAssessment → ⊥
queryCompilerDoesNotBypassAssessment ()

cheapestExecutionDoesNotAutomaticallyWin :
  CheapestExecutionAutomaticallyBestProofSearch → ⊥
cheapestExecutionDoesNotAutomaticallyWin ()
