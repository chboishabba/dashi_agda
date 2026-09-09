module DASHI.Law.SensibLawHistoricalLegalResearchOperatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawProofSearchExpansionBidiExact as Expansion

------------------------------------------------------------------------
-- HISTORICAL LAWYER RESEARCH OPERATORS
--
-- Traditional research progressively constructed a local authority subgraph:
-- issue classification -> leading authority -> noting up/treatment -> cited
-- authorities -> fact analogues -> refined issue. Secondary material often
-- supplied vocabulary and authority candidates without itself becoming the
-- binding proof payment.
------------------------------------------------------------------------

data HistoricalResearchMove : Set where
  digestOrSubjectClassification
  leadingAuthorityLookup
  noteUpInboundCitations
  inspectAuthoritiesCited
  inspectLegislationCited
  factPatternSearch
  secondarySourceVocabularyBridge
  textbookTreatiseBridge
  journalCommentaryBridge
  refinedIssueClassification
  : HistoricalResearchMove

record HistoricalResearchStep : Set₁ where
  constructor historicalResearchStep
  field
    intent : Intent.SearchIntent
    move : HistoricalResearchMove
    inputReference : String
    queryReference : String
    authorityReference : String
    outputResidualReference : String
    stepReference : String

open HistoricalResearchStep public

record HistoricalResearchTrace : Set₁ where
  constructor historicalResearchTrace
  field
    initialIssueReference : String
    steps : List HistoricalResearchStep
    resultingAuthorityNeighbourhoodReference : String
    resultingVocabularyReference : String
    resultingResidualReference : String
    traceReference : String

open HistoricalResearchTrace public

------------------------------------------------------------------------
-- Modern lowering of historical moves into the proof-search ABI.
------------------------------------------------------------------------

data ModernSearchOperationClass : Set where
  classificationExpansionOperation
  exactAuthorityOperation
  inboundCitationTraversalOperation
  outboundCitationTraversalOperation
  legislationTraversalOperation
  fullTextFactSearchOperation
  secondaryNavigationOperation
  : ModernSearchOperationClass

modernOperationFor : HistoricalResearchMove → ModernSearchOperationClass
modernOperationFor digestOrSubjectClassification = classificationExpansionOperation
modernOperationFor leadingAuthorityLookup = exactAuthorityOperation
modernOperationFor noteUpInboundCitations = inboundCitationTraversalOperation
modernOperationFor inspectAuthoritiesCited = outboundCitationTraversalOperation
modernOperationFor inspectLegislationCited = legislationTraversalOperation
modernOperationFor factPatternSearch = fullTextFactSearchOperation
modernOperationFor secondarySourceVocabularyBridge = secondaryNavigationOperation
modernOperationFor textbookTreatiseBridge = secondaryNavigationOperation
modernOperationFor journalCommentaryBridge = secondaryNavigationOperation
modernOperationFor refinedIssueClassification = classificationExpansionOperation

record HistoricalToModernSearchWeld : Set₁ where
  constructor historicalToModernSearchWeld
  field
    historicalStep : HistoricalResearchStep
    modernOperation : ModernSearchOperationClass
    operationMatchesMove :
      modernOperation ≡ modernOperationFor (move historicalStep)
    providerNeutralQueryReference : String
    citationTraversalReference : String
    expansionReference : String
    weldReference : String

open HistoricalToModernSearchWeld public

------------------------------------------------------------------------
-- Canonical sparse-world sequence.
------------------------------------------------------------------------

canonicalSparseResearchSequence : List HistoricalResearchMove
canonicalSparseResearchSequence =
  digestOrSubjectClassification
  ∷ leadingAuthorityLookup
  ∷ noteUpInboundCitations
  ∷ inspectAuthoritiesCited
  ∷ factPatternSearch
  ∷ refinedIssueClassification
  ∷ []

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DigestHeadingAutomaticallyRule : Set where
data LeadingCaseNameAutomaticallyCurrentAuthority : Set where
data NotingUpAutomaticallyMeansFollowed : Set where
data SecondarySourceAutomaticallyPaysPrimaryAuthorityGap : Set where
data HistoricalWorkflowRequiresCompleteWorldModel : Set where

digestHeadingDoesNotBecomeRule : DigestHeadingAutomaticallyRule → ⊥
digestHeadingDoesNotBecomeRule ()

leadingCaseNameDoesNotFixCurrentAuthority : LeadingCaseNameAutomaticallyCurrentAuthority → ⊥
leadingCaseNameDoesNotFixCurrentAuthority ()

notingUpDoesNotMeanFollowed : NotingUpAutomaticallyMeansFollowed → ⊥
notingUpDoesNotMeanFollowed ()

secondarySourceDoesNotPayPrimaryGap : SecondarySourceAutomaticallyPaysPrimaryAuthorityGap → ⊥
secondarySourceDoesNotPayPrimaryGap ()

historicalWorkflowDidNotRequireCompleteWorld : HistoricalWorkflowRequiresCompleteWorldModel → ⊥
historicalWorkflowDidNotRequireCompleteWorld ()

record HistoricalResearchBoundary : Set where
  constructor historicalResearchBoundary
  field
    historicalResearchBuildsSparseAuthoritySubgraph : Bool
    historicalResearchBuildsSparseAuthoritySubgraphIsTrue :
      historicalResearchBuildsSparseAuthoritySubgraph ≡ true
    notingUpMapsToCitationTraversal : Bool
    notingUpMapsToCitationTraversalIsTrue : notingUpMapsToCitationTraversal ≡ true
    secondarySourcesMapToNavigationExpansion : Bool
    secondarySourcesMapToNavigationExpansionIsTrue :
      secondarySourcesMapToNavigationExpansion ≡ true
    historicalMethodRequiresCompleteWorldFirst : Bool
    historicalMethodRequiresCompleteWorldFirstIsFalse :
      historicalMethodRequiresCompleteWorldFirst ≡ false

canonicalHistoricalResearchBoundary : HistoricalResearchBoundary
canonicalHistoricalResearchBoundary =
  historicalResearchBoundary true refl true refl true refl false refl
