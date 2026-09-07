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
import DASHI.Law.SensibLawSparseWorldModelAcquisitionExact as World
import DASHI.Law.SensibLawPrecedentGeometryStatisticsExact as Geometry
import DASHI.Law.SensibLawProofSearchExpansionBidiExact as Expansion
import DASHI.Law.SensibLawBidirectionalWorldLawProofSearchExact as Bidi
import DASHI.Law.SensibLawWaterproofArgumentGapSearchExact as Waterproof
import DASHI.Law.SensibLawTextWitnessTransmissionProvenanceExact as Witness
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
--   -> provider lowering or citation traversal
--   -> acquisition
--   -> same parser / PNF re-entry with witness lineage retained
--   -> proposition/authority/treatment assessment
--   -> proof payment / frontier delta
--   -> Pareto continuation or saturation
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
