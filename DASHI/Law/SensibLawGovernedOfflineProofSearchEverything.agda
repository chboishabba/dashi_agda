module DASHI.Law.SensibLawGovernedOfflineProofSearchEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedCorpusSearchEverything as Search
import DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact as Network
import DASHI.Law.SensibLawOfflineFirstProofSearchExecutionExact as Offline

------------------------------------------------------------------------
-- GOVERNED OFFLINE-FIRST PROOF-SEARCH CAPSTONE
------------------------------------------------------------------------

selectedSearchContract : Search.ProofDirectedCorpusSearchContract
selectedSearchContract = Search.canonicalProofDirectedCorpusSearchContract

selectedNetworkBoundary : Network.GovernedLegalNetworkBoundary
selectedNetworkBoundary = Network.canonicalGovernedLegalNetworkBoundary

selectedOfflineBoundary : Offline.OfflineFirstBoundary
selectedOfflineBoundary = Offline.canonicalOfflineFirstBoundary

record GovernedOfflineProofSearchContract : Set where
  constructor governedOfflineProofSearchContract
  field
    firstRuntimeNetworkFree : Bool
    firstRuntimeNetworkFreeIsTrue : firstRuntimeNetworkFree ≡ true
    localFixtureOrPersistedReceiptPrecedesLiveNetwork : Bool
    localFixtureOrPersistedReceiptPrecedesLiveNetworkIsTrue :
      localFixtureOrPersistedReceiptPrecedesLiveNetwork ≡ true
    liveLegalResearchIsSeparatelyGoverned : Bool
    liveLegalResearchIsSeparatelyGovernedIsTrue :
      liveLegalResearchIsSeparatelyGoverned ≡ true
    liveFollowRequiresPacingAndBounds : Bool
    liveFollowRequiresPacingAndBoundsIsTrue :
      liveFollowRequiresPacingAndBounds ≡ true
    parserRunsOnlyAfterLocalIngestion : Bool
    parserRunsOnlyAfterLocalIngestionIsTrue :
      parserRunsOnlyAfterLocalIngestion ≡ true
    directOperatorUtilityIsBatchProofFollow : Bool
    directOperatorUtilityIsBatchProofFollowIsFalse :
      directOperatorUtilityIsBatchProofFollow ≡ false

canonicalGovernedOfflineProofSearchContract : GovernedOfflineProofSearchContract
canonicalGovernedOfflineProofSearchContract =
  governedOfflineProofSearchContract
    true refl true refl true refl true refl true refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OfflineFirstMeansNeverUseNetwork : Set where
data NetworkAvailabilityMayTriggerResearchByItself : Set where
data PersistedReceiptMaySkipProofAssessment : Set where

offlineFirstDoesNotBanGovernedLaterNetwork : OfflineFirstMeansNeverUseNetwork → ⊥
offlineFirstDoesNotBanGovernedLaterNetwork ()

networkAvailabilityDoesNotTriggerResearch : NetworkAvailabilityMayTriggerResearchByItself → ⊥
networkAvailabilityDoesNotTriggerResearch ()

persistedReceiptDoesNotSkipAssessment : PersistedReceiptMaySkipProofAssessment → ⊥
persistedReceiptDoesNotSkipAssessment ()
