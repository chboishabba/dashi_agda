module DASHI.Law.SensibLawProofDirectedSearchIntentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue
import DASHI.Law.SensibLawLegalResidualProducerSchedulerExact as LegalResidual

------------------------------------------------------------------------
-- PROOF-DIRECTED SEARCH INTENT
--
-- The search engine does not begin with a provider or a string. It begins with
-- one consumer-relative proof gap, identifies the proposition/source shape
-- capable of paying that gap, and only then lowers to executable retrieval.
------------------------------------------------------------------------

data ProducerClass : Set where
  exactCitedAuthorityProducer : ProducerClass
  authorityDiscoveryProducer : ProducerClass
  authorityTreatmentProducer : ProducerClass
  propositionSourceProducer : ProducerClass
  doctrinalComparisonProducer : ProducerClass
  identityProducer : ProducerClass
  occurrenceEvidenceProducer : ProducerClass
  attributionProducer : ProducerClass
  temporalProducer : ProducerClass
  historicalContextProducer : ProducerClass
  empiricalEvidenceProducer : ProducerClass
  wrongTypeProducer : ProducerClass
  elementRequirementProducer : ProducerClass
  elementPaymentProducer : ProducerClass
  applicabilityProducer : ProducerClass
  jurisdictionProducer : ProducerClass
  remedySourceProducer : ProducerClass
  contradictionProducer : ProducerClass
  counterexampleProducer : ProducerClass
  discriminatorProducer : ProducerClass
  noSearchProducer : ProducerClass


data SearchMode : Set where
  exploitKnownResidual : SearchMode
  exploreVocabulary : SearchMode
  exploreAuthorityFamily : SearchMode
  compareAuthorities : SearchMode
  seekDefeater : SearchMode
  seekCounterexample : SearchMode
  noSearchRequired : SearchMode


data RequiredAuthorityClass : Set where
  bindingAuthorityPreferred : RequiredAuthorityClass
  persuasiveAuthorityPermitted : RequiredAuthorityClass
  primaryTextRequired : RequiredAuthorityClass
  supportingSourcePermitted : RequiredAuthorityClass
  authorityClassOpen : RequiredAuthorityClass


record SearchBudget : Set where
  constructor searchBudget
  field
    maxQueries : Nat
    maxDocuments : Nat
    maxCitationDepth : Nat
    budgetReference : String

open SearchBudget public

record SearchIntent : Set₁ where
  constructor searchIntent
  field
    consumerReference : String
    targetPropositionReference : String
    producerClass : ProducerClass
    mode : SearchMode
    jurisdictionReference : String
    temporalEnvelopeReference : String
    authorityClass : RequiredAuthorityClass
    structuralFibreReference : String
    knownAuthorityReference : String
    requiredTreatmentReference : String
    exclusionReference : String
    budget : SearchBudget
    intentReference : String

open SearchIntent public

------------------------------------------------------------------------
-- Adjudicative proof obligation -> producer class.
------------------------------------------------------------------------

producerForObligation : Issue.LegalProofObligation → ProducerClass
producerForObligation Issue.establishIssueProposition = propositionSourceProducer
producerForObligation Issue.allocateBurden = authorityDiscoveryProducer
producerForObligation Issue.establishStandard = authorityDiscoveryProducer
producerForObligation Issue.establishEvidenceAdequacy = occurrenceEvidenceProducer
producerForObligation Issue.establishAuthority = authorityDiscoveryProducer
producerForObligation Issue.establishJurisdiction = jurisdictionProducer
producerForObligation Issue.establishTemporalValidity = temporalProducer
producerForObligation Issue.establishApplicability = applicabilityProducer
producerForObligation Issue.establishViolation = elementPaymentProducer
producerForObligation Issue.establishLiability = discriminatorProducer
producerForObligation Issue.establishHarm = occurrenceEvidenceProducer
producerForObligation Issue.establishProtectedInterest = elementRequirementProducer
producerForObligation Issue.establishRemedySource = remedySourceProducer
producerForObligation Issue.explainDisposition = doctrinalComparisonProducer
producerForObligation Issue.noFurtherObligation = discriminatorProducer

modeForWork : Issue.EpistemicWorkKind → SearchMode
modeForWork Issue.lookWork = exploitKnownResidual
modeForWork Issue.testWork = seekCounterexample
modeForWork Issue.thinkWork = compareAuthorities
modeForWork Issue.actWork = exploreAuthorityFamily
modeForWork Issue.noWork = exploitKnownResidual

record CompiledProofDirectedIntent : Set₁ where
  constructor compiledProofDirectedIntent
  field
    compiledSearch : Issue.CompiledAdjudicativeSearch
    intent : SearchIntent
    producerMatchesObligation :
      producerClass intent ≡ producerForObligation (Issue.obligation compiledSearch)
    modeMatchesWork :
      mode intent ≡ modeForWork (Issue.workKind compiledSearch)
    compilationReference : String

open CompiledProofDirectedIntent public

------------------------------------------------------------------------
-- Legal-adjunct residual bridge. This does not broaden blocked source plans.
------------------------------------------------------------------------

data ResidualSearchDisposition : Set where
  residualCanCompileToSearch : ResidualSearchDisposition
  residualRequiresNonSearchReview : ResidualSearchDisposition
  residualBlockedBeforeSearch : ResidualSearchDisposition


searchDisposition : LegalResidual.LegalResidualKind → ResidualSearchDisposition
searchDisposition LegalResidual.legalRelevanceUnresolved = residualCanCompileToSearch
searchDisposition LegalResidual.legalAuthorityAbsent = residualCanCompileToSearch
searchDisposition LegalResidual.legalApplicabilityUnresolved = residualRequiresNonSearchReview
searchDisposition LegalResidual.legalInterpretationUnresolved = residualCanCompileToSearch
searchDisposition LegalResidual.legalElementPaymentMissing = residualCanCompileToSearch

------------------------------------------------------------------------
-- Search-intent firewalls.
------------------------------------------------------------------------

data SearchStringDefinesResearchIntent : Set where
data ProviderDefinesProofObligation : Set where
data SearchHitAutomaticallyPaysProofGap : Set where
data MoreDocumentsAutomaticallyImproveProof : Set where
data SupportingSearchMayOmitDefeaterSearch : Set where

searchStringDoesNotDefineIntent : SearchStringDefinesResearchIntent → ⊥
searchStringDoesNotDefineIntent ()

providerDoesNotDefineProofObligation : ProviderDefinesProofObligation → ⊥
providerDoesNotDefineProofObligation ()

searchHitDoesNotPayGapByExistence : SearchHitAutomaticallyPaysProofGap → ⊥
searchHitDoesNotPayGapByExistence ()

moreDocumentsDoNotAutomaticallyImproveProof : MoreDocumentsAutomaticallyImproveProof → ⊥
moreDocumentsDoNotAutomaticallyImproveProof ()

supportSearchDoesNotEraseDefeaterDuty : SupportingSearchMayOmitDefeaterSearch → ⊥
supportSearchDoesNotEraseDefeaterDuty ()

record ProofDirectedSearchBoundary : Set where
  constructor proofDirectedSearchBoundary
  field
    proofGapPrecedesProviderSelection : Bool
    proofGapPrecedesProviderSelectionIsTrue : proofGapPrecedesProviderSelection ≡ true
    producerClassPrecedesExecutableQuery : Bool
    producerClassPrecedesExecutableQueryIsTrue : producerClassPrecedesExecutableQuery ≡ true
    providerMayInventProofObligation : Bool
    providerMayInventProofObligationIsFalse : providerMayInventProofObligation ≡ false
    retrievalEqualsProofPayment : Bool
    retrievalEqualsProofPaymentIsFalse : retrievalEqualsProofPayment ≡ false
    explorationMayRemainExplicit : Bool
    explorationMayRemainExplicitIsTrue : explorationMayRemainExplicit ≡ true

canonicalProofDirectedSearchBoundary : ProofDirectedSearchBoundary
canonicalProofDirectedSearchBoundary =
  proofDirectedSearchBoundary true refl true refl false refl false refl true refl
