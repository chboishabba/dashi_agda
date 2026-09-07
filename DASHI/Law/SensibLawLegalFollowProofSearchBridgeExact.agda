module DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawLegalResidualProducerSchedulerExact as Scheduler
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawCorpusProducerRoutingExact as Corpus
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query

------------------------------------------------------------------------
-- LEGAL-FOLLOW -> PROOF-SEARCH BRIDGE
--
-- The historical SensibLaw adapter already knows how to execute a ready typed
-- source plan without broadening provider/jurisdiction constraints. This Agda
-- owner specifies how such a plan is reached from a proof gap and how its
-- results return to the proof-search algebra.
------------------------------------------------------------------------

record ReadyLegalFollowSearchBridge : Set₁ where
  constructor readyLegalFollowSearchBridge
  field
    residualDemand : Scheduler.LegalResidualDemand
    searchIntent : Intent.SearchIntent
    residualIsSearchable :
      Intent.searchDisposition (Scheduler.residual residualDemand)
      ≡ Intent.residualCanCompileToSearch
    structuralSignatureReference : String
    jurisdictionReference : String
    sourceRoleReference : String
    authorityLevelReference : String
    sameReadyPlanReceipt : Set
    eligibleCorpusClasses : List Corpus.CorpusClass
    eligibleCorporaMatchProducerReceipt : Set
    queryFamilyReference : String
    bridgeReference : String

open ReadyLegalFollowSearchBridge public

record LegalFollowQueryExecution : Set₁ where
  constructor legalFollowQueryExecution
  field
    bridge : ReadyLegalFollowSearchBridge
    compiledQuery : Query.ProviderCompiledQuery
    queryMatchesIntentReceipt : Set
    selectedEndpointMatchesTypedPlanReceipt : Set
    boundedAcquisitionReference : String
    sameParserPNFReentryReference : String
    executionReference : String

open LegalFollowQueryExecution public

record LegalFollowGraphExecution : Set₁ where
  constructor legalFollowGraphExecution
  field
    bridge : ReadyLegalFollowSearchBridge
    traversal : Query.CitationTraversal
    traversalMatchesAuthorityProducerReceipt : Set
    boundedAcquisitionReference : String
    sameParserPNFReentryReference : String
    executionReference : String

open LegalFollowGraphExecution public

------------------------------------------------------------------------
-- Blocked legal-follow plans remain blocked at search compilation.
------------------------------------------------------------------------

record BlockedLegalFollowSearchBridge : Set where
  constructor blockedLegalFollowSearchBridge
  field
    blockedDemand : Scheduler.BlockedLegalResidualDemand
    noExecutableQueryReceipt : Set
    noProviderBroadeningReceipt : Set
    blockedReference : String

open BlockedLegalFollowSearchBridge public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReadyPlanMayIgnoreProofGap : Set where
data BlockedPlanMayCompileBroadSearch : Set where
data SearchCompilerMayChangeJurisdiction : Set where
data LegalFollowAcquisitionAutomaticallyPaysResidual : Set where
data ProviderFallbackMayEscapeTypedSourceRole : Set where

readyPlanDoesNotIgnoreProofGap : ReadyPlanMayIgnoreProofGap → ⊥
readyPlanDoesNotIgnoreProofGap ()

blockedPlanDoesNotCompileBroadSearch : BlockedPlanMayCompileBroadSearch → ⊥
blockedPlanDoesNotCompileBroadSearch ()

searchCompilerDoesNotChangeJurisdiction : SearchCompilerMayChangeJurisdiction → ⊥
searchCompilerDoesNotChangeJurisdiction ()

acquisitionDoesNotAutoPayResidual : LegalFollowAcquisitionAutomaticallyPaysResidual → ⊥
acquisitionDoesNotAutoPayResidual ()

providerFallbackDoesNotEscapeSourceRole : ProviderFallbackMayEscapeTypedSourceRole → ⊥
providerFallbackDoesNotEscapeSourceRole ()

record LegalFollowProofSearchBoundary : Set where
  constructor legalFollowProofSearchBoundary
  field
    proofGapPrecedesLegalFollowQuery : Bool
    proofGapPrecedesLegalFollowQueryIsTrue : proofGapPrecedesLegalFollowQuery ≡ true
    readyPlanConstraintsSurviveQueryCompilation : Bool
    readyPlanConstraintsSurviveQueryCompilationIsTrue :
      readyPlanConstraintsSurviveQueryCompilation ≡ true
    blockedPlanBroadens : Bool
    blockedPlanBroadensIsFalse : blockedPlanBroadens ≡ false
    acquisitionEqualsResidualPayment : Bool
    acquisitionEqualsResidualPaymentIsFalse : acquisitionEqualsResidualPayment ≡ false

canonicalLegalFollowProofSearchBoundary : LegalFollowProofSearchBoundary
canonicalLegalFollowProofSearchBoundary =
  legalFollowProofSearchBoundary true refl true refl false refl false refl
