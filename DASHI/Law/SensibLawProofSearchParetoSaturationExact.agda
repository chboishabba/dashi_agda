module DASHI.Law.SensibLawProofSearchParetoSaturationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result

------------------------------------------------------------------------
-- LEGAL SEARCH PARETO SURFACE
--
-- Search is not ranked by one confidence/relevance scalar. The legal search
-- consumer keeps separate proof-reduction, discrimination, authority fitness,
-- novelty, coverage gain and cost coordinates.
------------------------------------------------------------------------

record SearchValueVector : Set where
  constructor searchValueVector
  field
    expectedProofReduction : Nat
    discriminativeValue : Nat
    authorityFitness : Nat
    novelty : Nat
    coverageGain : Nat
    acquisitionCost : Nat
    calibrationReference : String

open SearchValueVector public

record SearchCandidate : Set₁ where
  constructor searchCandidate
  field
    hypothesis : Query.SearchHypothesis
    value : SearchValueVector
    admissibilityReceipt : Set
    candidateReference : String

open SearchCandidate public

record SearchDominates (left right : SearchCandidate) : Set where
  constructor searchDominates
  field
    noLessProofReduction :
      expectedProofReduction (value right) ≤ expectedProofReduction (value left)
    noLessDiscriminativeValue :
      discriminativeValue (value right) ≤ discriminativeValue (value left)
    noLessAuthorityFitness :
      authorityFitness (value right) ≤ authorityFitness (value left)
    noLessNovelty : novelty (value right) ≤ novelty (value left)
    noLessCoverageGain : coverageGain (value right) ≤ coverageGain (value left)
    noMoreCost : acquisitionCost (value left) ≤ acquisitionCost (value right)

open SearchDominates public

record SearchParetoChoice
    (Declared : SearchCandidate → Set) : Set₂ where
  constructor searchParetoChoice
  field
    selected : SearchCandidate
    selectedDeclared : Declared selected
    undominated :
      (alternative : SearchCandidate) →
      Declared alternative →
      SearchDominates alternative selected →
      SearchDominates selected alternative
    choiceReference : String

open SearchParetoChoice public

------------------------------------------------------------------------
-- Reuse of the generic residual-information owner.
------------------------------------------------------------------------

proofSearchMoveKindIsExistingGenericMove :
  Costed.ResidualInformationMoveKind
proofSearchMoveKindIsExistingGenericMove = Costed.proofSearchResidualMove

sourceRecoveryMoveKindIsExistingGenericMove :
  Costed.ResidualInformationMoveKind
sourceRecoveryMoveKindIsExistingGenericMove = Costed.sourceRecoveryResidualMove

record SearchParetoRefinementBoundary : Set where
  constructor searchParetoRefinementBoundary
  field
    genericCostGainOwnerReused : Bool
    genericCostGainOwnerReusedIsTrue : genericCostGainOwnerReused ≡ true
    legalSearchAddsIndependentAxes : Bool
    legalSearchAddsIndependentAxesIsTrue : legalSearchAddsIndependentAxes ≡ true
    axesAreScalarisedIntoConfidence : Bool
    axesAreScalarisedIntoConfidenceIsFalse : axesAreScalarisedIntoConfidence ≡ false

canonicalSearchParetoRefinementBoundary : SearchParetoRefinementBoundary
canonicalSearchParetoRefinementBoundary =
  searchParetoRefinementBoundary true refl true refl false refl

------------------------------------------------------------------------
-- SATURATION / STOPPING CALCULUS
------------------------------------------------------------------------

data AcquisitionFamily : Set where
  exactCitationFamily : AcquisitionFamily
  inboundCitationFamily : AcquisitionFamily
  outboundCitationFamily : AcquisitionFamily
  doctrinalTextSearchFamily : AcquisitionFamily
  factPatternFamily : AcquisitionFamily
  secondaryVocabularyFamily : AcquisitionFamily
  defeaterFamily : AcquisitionFamily
  comparatorFamily : AcquisitionFamily
  contradictionFamily : AcquisitionFamily
  localWorldGraphFamily : AcquisitionFamily


record SearchRound : Set₁ where
  constructor searchRound
  field
    consumerReference : String
    acquisitionFamily : AcquisitionFamily
    resultDeltas : List Result.SearchFrontierDelta
    nonProgressingResults : List Result.NonProgressingSearchResult
    roundReference : String

open SearchRound public

record SearchSaturationReceipt : Set₁ where
  constructor searchSaturationReceipt
  field
    consumerReference : String
    independentFamiliesInspected : List AcquisitionFamily
    priorFrontierReference : String
    currentFrontierReference : String
    frontierStableReceipt : Set
    allNewResultsDuplicateDominatedSameContributionOrAuthorityInferiorReceipt : Set
    expectedFrontierReductionExhaustedReceipt : Set
    stoppingReference : String

open SearchSaturationReceipt public

data SearchContinuationDecision : Set where
  continueExploit : SearchContinuationDecision
  continueExplore : SearchContinuationDecision
  stopAtEmpiricalSaturation : SearchContinuationDecision
  stopAuthorityBlocked : SearchContinuationDecision
  stopUnderidentified : SearchContinuationDecision


------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CheapestSearchAutomaticallyBestSearch : Set where
data MostRelevantSearchAutomaticallyAuthorityFit : Set where
data FrontierUnchangedOnceMeansSaturated : Set where
data SaturatedSearchMeansLegalPropositionFalse : Set where
data SaturatedSearchMeansConsumerProofClosed : Set where

data LargeCorpusAutomaticallyHighInformationGain : Set where

cheapestDoesNotMeanBest : CheapestSearchAutomaticallyBestSearch → ⊥
cheapestDoesNotMeanBest ()

relevanceDoesNotMeanAuthorityFitness : MostRelevantSearchAutomaticallyAuthorityFit → ⊥
relevanceDoesNotMeanAuthorityFitness ()

oneUnchangedRoundDoesNotMeanSaturation : FrontierUnchangedOnceMeansSaturated → ⊥
oneUnchangedRoundDoesNotMeanSaturation ()

saturationDoesNotMeanFalse : SaturatedSearchMeansLegalPropositionFalse → ⊥
saturationDoesNotMeanFalse ()

saturationDoesNotMeanProofClosed : SaturatedSearchMeansConsumerProofClosed → ⊥
saturationDoesNotMeanProofClosed ()

largeCorpusDoesNotGuaranteeGain : LargeCorpusAutomaticallyHighInformationGain → ⊥
largeCorpusDoesNotGuaranteeGain ()

record SearchSaturationBoundary : Set where
  constructor searchSaturationBoundary
  field
    saturationIsFrontierRelative : Bool
    saturationIsFrontierRelativeIsTrue : saturationIsFrontierRelative ≡ true
    independentAcquisitionFamiliesMatter : Bool
    independentAcquisitionFamiliesMatterIsTrue : independentAcquisitionFamiliesMatter ≡ true
    fixedDocumentCountDefinesSaturation : Bool
    fixedDocumentCountDefinesSaturationIsFalse : fixedDocumentCountDefinesSaturation ≡ false
    saturationEqualsProof : Bool
    saturationEqualsProofIsFalse : saturationEqualsProof ≡ false

canonicalSearchSaturationBoundary : SearchSaturationBoundary
canonicalSearchSaturationBoundary =
  searchSaturationBoundary true refl true refl false refl false refl
