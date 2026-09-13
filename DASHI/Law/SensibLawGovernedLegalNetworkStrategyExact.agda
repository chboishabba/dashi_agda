module DASHI.Law.SensibLawGovernedLegalNetworkStrategyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawProofGapExecutableSearchCompilerExact as Compiler

------------------------------------------------------------------------
-- GOVERNED LIVE LEGAL NETWORK STRATEGY
--
-- Network access is an execution strategy subordinate to an already-typed
-- proof-search plan. The first production runtime may remain entirely offline.
-- Live AustLII/JADE access is separately governed by pacing, breadth/depth,
-- cache preference, and search-reference/fetch-bytes separation.
------------------------------------------------------------------------

data LegalNetworkMode : Set where
  localFixtureOnly
  persistedAuthorityReceiptOnly
  governedLiveLegalAdapter
  : LegalNetworkMode

data LegalAcquisitionOperation : Set where
  searchReferencesOnly
  fetchExplicitDocumentBytes
  deterministicKnownAuthorityResolution
  boundedCitationFollow
  : LegalAcquisitionOperation

record LegalHostPacingPolicy : Set where
  constructor legalHostPacingPolicy
  field
    requestsPerFourSeconds : Nat
    burstLimit : Nat
    pacingReference : String

open LegalHostPacingPolicy public

canonicalLegalHostPacing : LegalHostPacingPolicy
canonicalLegalHostPacing = legalHostPacingPolicy 1 1
  "SensibLaw legal-host default: 0.25 requests/second, burst 1"

record LegalFollowBounds : Set where
  constructor legalFollowBounds
  field
    maxDepth : Nat
    maxNewDocuments : Nat
    boundsExplicitReceipt : Set
    boundsReference : String

open LegalFollowBounds public

record GovernedLiveLegalExecution : Set₁ where
  constructor governedLiveLegalExecution
  field
    proofPlan : Compiler.ProofGapSearchPlan
    providerQuery : Query.ProviderCompiledQuery
    queryComesFromProofPlanReceipt : Set
    mode : LegalNetworkMode
    modeIsGovernedLive : mode ≡ governedLiveLegalAdapter
    operation : LegalAcquisitionOperation
    pacing : LegalHostPacingPolicy
    followBounds : LegalFollowBounds
    localCacheCheckedFirstReceipt : Set
    persistedAuthorityReceiptCheckedFirstReceipt : Set
    noCrawlingReceipt : Set
    noAdHocPollingReceipt : Set
    searchReturnsReferencesReceipt : Set
    fetchReturnsBytesReceipt : Set
    parserBeginsOnlyAfterLocalIngestionReceipt : Set
    governedExecutionReference : String

open GovernedLiveLegalExecution public

record DirectOperatorUtilityBoundary : Set where
  constructor directOperatorUtilityBoundary
  field
    utilityReference : String
    directlyUsesNetworkPrimitive : Bool
    admissibleForBatchProofFollowWithoutGovernedWrapper : Bool
    admissibleForBatchProofFollowWithoutGovernedWrapperIsFalse :
      admissibleForBatchProofFollowWithoutGovernedWrapper ≡ false

open DirectOperatorUtilityBoundary public

acquireLegalSourceBoundary : DirectOperatorUtilityBoundary
acquireLegalSourceBoundary = directOperatorUtilityBoundary
  "scripts/acquire_legal_source.py"
  true
  false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProofGapMayTriggerUngovernedNetwork : Set where
data SearchReferenceMayBeParsedAsDocumentBytes : Set where
data FetchBytesMayBypassLocalIngestion : Set where
data LiveAdapterMayIgnoreDepthOrBreadth : Set where
data DirectUrlopenUtilityIsGovernedBatchFollow : Set where

proofGapDoesNotTriggerUngovernedNetwork : ProofGapMayTriggerUngovernedNetwork → ⊥
proofGapDoesNotTriggerUngovernedNetwork ()

searchReferenceDoesNotBecomeDocumentBytes : SearchReferenceMayBeParsedAsDocumentBytes → ⊥
searchReferenceDoesNotBecomeDocumentBytes ()

fetchDoesNotBypassIngestion : FetchBytesMayBypassLocalIngestion → ⊥
fetchDoesNotBypassIngestion ()

liveAdapterDoesNotIgnoreBounds : LiveAdapterMayIgnoreDepthOrBreadth → ⊥
liveAdapterDoesNotIgnoreBounds ()

directUrlopenIsNotGovernedBatchFollow : DirectUrlopenUtilityIsGovernedBatchFollow → ⊥
directUrlopenIsNotGovernedBatchFollow ()

record GovernedLegalNetworkBoundary : Set where
  constructor governedLegalNetworkBoundary
  field
    networkIsSeparateExecutionStrategy : Bool
    networkIsSeparateExecutionStrategyIsTrue : networkIsSeparateExecutionStrategy ≡ true
    liveAccessRequiresGovernance : Bool
    liveAccessRequiresGovernanceIsTrue : liveAccessRequiresGovernance ≡ true
    localCachePreferred : Bool
    localCachePreferredIsTrue : localCachePreferred ≡ true
    parserMayRunBeforeLocalIngestion : Bool
    parserMayRunBeforeLocalIngestionIsFalse : parserMayRunBeforeLocalIngestion ≡ false
    crawlingPermitted : Bool
    crawlingPermittedIsFalse : crawlingPermitted ≡ false
    firstRuntimeMustUseNetwork : Bool
    firstRuntimeMustUseNetworkIsFalse : firstRuntimeMustUseNetwork ≡ false

canonicalGovernedLegalNetworkBoundary : GovernedLegalNetworkBoundary
canonicalGovernedLegalNetworkBoundary =
  governedLegalNetworkBoundary true refl true refl true refl false refl false refl false refl
