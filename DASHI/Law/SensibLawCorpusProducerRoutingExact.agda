module DASHI.Law.SensibLawCorpusProducerRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent

------------------------------------------------------------------------
-- PRODUCER-INDEXED CORPUS ROUTING
------------------------------------------------------------------------

data CorpusClass : Set where
  localCompiledWorldCorpus : CorpusClass
  officialCaseLawCorpus : CorpusClass
  researchCaseLawIndex : CorpusClass
  officialLegislationCorpus : CorpusClass
  regulationAndStandardCorpus : CorpusClass
  wikipediaCorpus : CorpusClass
  wikidataCorpus : CorpusClass
  journalCorpus : CorpusClass
  bookAndTreatiseCorpus : CorpusClass
  lawReformAndGovernmentReportCorpus : CorpusClass
  transcriptAndTestimonyCorpus : CorpusClass
  matterDocumentCorpus : CorpusClass
  archivalHistoricalCorpus : CorpusClass
  generalFreeTextCorpus : CorpusClass


eligibleCorpora : Intent.ProducerClass → List CorpusClass
eligibleCorpora Intent.exactCitedAuthorityProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ researchCaseLawIndex ∷ []
eligibleCorpora Intent.authorityDiscoveryProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ researchCaseLawIndex ∷ journalCorpus ∷ bookAndTreatiseCorpus ∷ []
eligibleCorpora Intent.authorityTreatmentProducer =
  localCompiledWorldCorpus ∷ researchCaseLawIndex ∷ officialCaseLawCorpus ∷ []
eligibleCorpora Intent.propositionSourceProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ officialLegislationCorpus ∷ transcriptAndTestimonyCorpus ∷ matterDocumentCorpus ∷ []
eligibleCorpora Intent.doctrinalComparisonProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ researchCaseLawIndex ∷ journalCorpus ∷ bookAndTreatiseCorpus ∷ []
eligibleCorpora Intent.identityProducer =
  localCompiledWorldCorpus ∷ wikidataCorpus ∷ wikipediaCorpus ∷ generalFreeTextCorpus ∷ []
eligibleCorpora Intent.occurrenceEvidenceProducer =
  localCompiledWorldCorpus ∷ matterDocumentCorpus ∷ transcriptAndTestimonyCorpus ∷ journalCorpus ∷ lawReformAndGovernmentReportCorpus ∷ []
eligibleCorpora Intent.attributionProducer =
  localCompiledWorldCorpus ∷ matterDocumentCorpus ∷ transcriptAndTestimonyCorpus ∷ officialCaseLawCorpus ∷ []
eligibleCorpora Intent.temporalProducer =
  localCompiledWorldCorpus ∷ officialLegislationCorpus ∷ officialCaseLawCorpus ∷ archivalHistoricalCorpus ∷ []
eligibleCorpora Intent.historicalContextProducer =
  localCompiledWorldCorpus ∷ archivalHistoricalCorpus ∷ journalCorpus ∷ bookAndTreatiseCorpus ∷ wikipediaCorpus ∷ []
eligibleCorpora Intent.empiricalEvidenceProducer =
  localCompiledWorldCorpus ∷ journalCorpus ∷ lawReformAndGovernmentReportCorpus ∷ matterDocumentCorpus ∷ []
eligibleCorpora Intent.wrongTypeProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ officialLegislationCorpus ∷ regulationAndStandardCorpus ∷ []
eligibleCorpora Intent.elementRequirementProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ officialLegislationCorpus ∷ regulationAndStandardCorpus ∷ []
eligibleCorpora Intent.elementPaymentProducer =
  localCompiledWorldCorpus ∷ matterDocumentCorpus ∷ transcriptAndTestimonyCorpus ∷ journalCorpus ∷ []
eligibleCorpora Intent.applicabilityProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ officialLegislationCorpus ∷ []
eligibleCorpora Intent.jurisdictionProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ officialLegislationCorpus ∷ []
eligibleCorpora Intent.remedySourceProducer =
  localCompiledWorldCorpus ∷ officialLegislationCorpus ∷ officialCaseLawCorpus ∷ regulationAndStandardCorpus ∷ []
eligibleCorpora Intent.contradictionProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ journalCorpus ∷ matterDocumentCorpus ∷ []
eligibleCorpora Intent.counterexampleProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ matterDocumentCorpus ∷ journalCorpus ∷ []
eligibleCorpora Intent.discriminatorProducer =
  localCompiledWorldCorpus ∷ officialCaseLawCorpus ∷ researchCaseLawIndex ∷ journalCorpus ∷ bookAndTreatiseCorpus ∷ []
eligibleCorpora Intent.noSearchProducer = []

------------------------------------------------------------------------
-- Source capability boundary.
------------------------------------------------------------------------

record SourceCapability : Set where
  constructor sourceCapability
  field
    corpusClass : CorpusClass
    mayProposeIdentity : Bool
    mayProposeHistoricalContext : Bool
    maySupplyPrimaryLegalText : Bool
    maySupplyEmpiricalEvidence : Bool
    maySupplyMatterEvidence : Bool
    mayByExistenceEstablishLegalAuthority : Bool
    mayByExistenceEstablishTruth : Bool
    mayByExistenceEstablishApplicability : Bool

open SourceCapability public

wikipediaCapability : SourceCapability
wikipediaCapability = sourceCapability
  wikipediaCorpus true true false false false false false false

wikidataCapability : SourceCapability
wikidataCapability = sourceCapability
  wikidataCorpus true true false false false false false false

journalCapability : SourceCapability
journalCapability = sourceCapability
  journalCorpus false true false true false false false false

officialCaseCapability : SourceCapability
officialCaseCapability = sourceCapability
  officialCaseLawCorpus false false true false false false false false

officialLegislationCapability : SourceCapability
officialLegislationCapability = sourceCapability
  officialLegislationCorpus false false true false false false false false

matterDocumentCapability : SourceCapability
matterDocumentCapability = sourceCapability
  matterDocumentCorpus false false false false true false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data WikipediaAutomaticallyLegalAuthority : Set where
data WikidataAutomaticallyOccurrenceTruth : Set where
data JournalAutomaticallyBindingRule : Set where
data JudgmentAutomaticallyUniversalFact : Set where
data LegislationAutomaticallyAppliesToMatter : Set where
data MatterEvidenceAutomaticallyCreatesLegalRule : Set where
data ProviderClassMayOverrideProducerClass : Set where
data NoSearchProducerMayAcquireCorpus : Set where

wikipediaDoesNotBecomeLegalAuthority : WikipediaAutomaticallyLegalAuthority → ⊥
wikipediaDoesNotBecomeLegalAuthority ()

wikidataDoesNotBecomeOccurrenceTruth : WikidataAutomaticallyOccurrenceTruth → ⊥
wikidataDoesNotBecomeOccurrenceTruth ()

journalDoesNotBecomeBindingRule : JournalAutomaticallyBindingRule → ⊥
journalDoesNotBecomeBindingRule ()

judgmentDoesNotBecomeUniversalFact : JudgmentAutomaticallyUniversalFact → ⊥
judgmentDoesNotBecomeUniversalFact ()

legislationDoesNotAutomaticallyApply : LegislationAutomaticallyAppliesToMatter → ⊥
legislationDoesNotAutomaticallyApply ()

matterEvidenceDoesNotCreateRule : MatterEvidenceAutomaticallyCreatesLegalRule → ⊥
matterEvidenceDoesNotCreateRule ()

providerDoesNotOverrideProducer : ProviderClassMayOverrideProducerClass → ⊥
providerDoesNotOverrideProducer ()

noSearchProducerDoesNotAcquire : NoSearchProducerMayAcquireCorpus → ⊥
noSearchProducerDoesNotAcquire ()

record CorpusRoutingBoundary : Set where
  constructor corpusRoutingBoundary
  field
    producerPrecedesCorpusSelection : Bool
    producerPrecedesCorpusSelectionIsTrue : producerPrecedesCorpusSelection ≡ true
    wikipediaMayNavigateWithoutLegalAuthority : Bool
    wikipediaMayNavigateWithoutLegalAuthorityIsTrue :
      wikipediaMayNavigateWithoutLegalAuthority ≡ true
    wikidataMayProposeIdentityWithoutTruth : Bool
    wikidataMayProposeIdentityWithoutTruthIsTrue :
      wikidataMayProposeIdentityWithoutTruth ≡ true
    worldEvidenceEqualsLegalAuthority : Bool
    worldEvidenceEqualsLegalAuthorityIsFalse : worldEvidenceEqualsLegalAuthority ≡ false
    closedConsumerHasEligibleCorpus : Bool
    closedConsumerHasEligibleCorpusIsFalse : closedConsumerHasEligibleCorpus ≡ false

canonicalCorpusRoutingBoundary : CorpusRoutingBoundary
canonicalCorpusRoutingBoundary =
  corpusRoutingBoundary true refl true refl true refl false refl false refl
