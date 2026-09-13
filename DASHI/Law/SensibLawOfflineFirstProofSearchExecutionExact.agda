module DASHI.Law.SensibLawOfflineFirstProofSearchExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofGapExecutableSearchCompilerExact as Compiler
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Result
import DASHI.Law.SensibLawSparseWorldModelAcquisitionExact as World
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network

------------------------------------------------------------------------
-- OFFLINE-FIRST PRODUCTION ACCEPTANCE PATH
--
-- First Rust/SLR implementation target:
-- proof gap -> typed bounded provider-neutral plan -> local fixture/persisted
-- authority receipt -> local parser/PNF re-entry -> frontier delta.
-- No network capability is required to validate this semantic/runtime path.
------------------------------------------------------------------------

data OfflineAuthorityInputKind : Set where
  savedSearchFixture
  persistedAuthorityReceipt
  locallyIngestedPrimaryAuthority
  localCompiledWorldArtifact
  : OfflineAuthorityInputKind

record OfflineAuthorityInput : Set₁ where
  constructor offlineAuthorityInput
  field
    inputKind : OfflineAuthorityInputKind
    sourceIdentityReference : String
    localArtifactReference : String
    wholeFetchProvenanceReference : String
    selectedSegmentReference : String
    immutableReceiptReference : String
    inputReference : String

open OfflineAuthorityInput public

record OfflineProofSearchExecution : Set₁ where
  constructor offlineProofSearchExecution
  field
    plan : Compiler.ProofGapSearchPlan
    authorityInput : OfflineAuthorityInput
    planSatisfiedByLocalInputReceipt : Set
    networkMode : Network.LegalNetworkMode
    networkModeIsLocal : networkMode ≡ Network.localFixtureOnly
    localIngestionReceipt : Set
    parserPNFReentryReference : String
    compiledArtifact : World.CompiledCorpusArtifact
    passage : Result.RetrievedPassage
    attributedProposition : Result.AttributedSearchProposition passage
    assessment : Result.SearchResultProofAssessment attributedProposition
    frontierDelta : Result.SearchFrontierDelta
    sameConsumerReceipt : Set
    executionReference : String

open OfflineProofSearchExecution public

record PersistedReceiptProofSearchExecution : Set₁ where
  constructor persistedReceiptProofSearchExecution
  field
    plan : Compiler.ProofGapSearchPlan
    authorityInput : OfflineAuthorityInput
    networkMode : Network.LegalNetworkMode
    networkModeIsPersisted : networkMode ≡ Network.persistedAuthorityReceiptOnly
    noLiveNetworkReceipt : Set
    parserPNFReentryReference : String
    frontierDelta : Result.SearchFrontierDelta
    executionReference : String

open PersistedReceiptProofSearchExecution public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OfflineFixtureMeansAuthorityTrue : Set where
data PersistedReceiptMeansProofPaid : Set where
data OfflineExecutionMaySkipAssessment : Set where
data FirstRuntimeNeedsLiveAustLIIOrJADE : Set where

offlineFixtureDoesNotMeanAuthorityTrue : OfflineFixtureMeansAuthorityTrue → ⊥
offlineFixtureDoesNotMeanAuthorityTrue ()

persistedReceiptDoesNotMeanProofPaid : PersistedReceiptMeansProofPaid → ⊥
persistedReceiptDoesNotMeanProofPaid ()

offlineExecutionDoesNotSkipAssessment : OfflineExecutionMaySkipAssessment → ⊥
offlineExecutionDoesNotSkipAssessment ()

firstRuntimeDoesNotNeedLiveNetwork : FirstRuntimeNeedsLiveAustLIIOrJADE → ⊥
firstRuntimeDoesNotNeedLiveNetwork ()

record OfflineFirstBoundary : Set where
  constructor offlineFirstBoundary
  field
    firstRuntimeCanBeNetworkFree : Bool
    firstRuntimeCanBeNetworkFreeIsTrue : firstRuntimeCanBeNetworkFree ≡ true
    persistedReceiptsAreAdmissibleRuntimeInputs : Bool
    persistedReceiptsAreAdmissibleRuntimeInputsIsTrue :
      persistedReceiptsAreAdmissibleRuntimeInputs ≡ true
    localInputStillReentersParserPNF : Bool
    localInputStillReentersParserPNFIsTrue : localInputStillReentersParserPNF ≡ true
    localInputAutomaticallyPaysGap : Bool
    localInputAutomaticallyPaysGapIsFalse : localInputAutomaticallyPaysGap ≡ false

canonicalOfflineFirstBoundary : OfflineFirstBoundary
canonicalOfflineFirstBoundary =
  offlineFirstBoundary true refl true refl true refl false refl
