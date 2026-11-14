{-# OPTIONS --safe #-}
module DASHI.Biology.LysergicPriorArtFiniteCore where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- GOLDEN, NON-OPERATIONAL SOURCE-EVIDENCE GUARDS.
--
-- Original source authors/inventors:
-- Sarah L. Robinson; Daniel G. Panaccione (2014 article and patent family).
-- Wong, Lim, Tan, Go, Bell, Freemont and Yew (2022 yeast article).
--
-- These are finite-granularity classification theorems. They do not
-- prove biological activity, a legal conclusion, novelty, or a method.
-- No postulates, holes, nontermination or unsound compiler options.
------------------------------------------------------------------------

data NoWitness : Set where

data SourceObject : Set where
  researchArticle2014 : SourceObject
  patentPublication2015 : SourceObject
  yeastArticle2022 : SourceObject
  yeastPatentPublication2023 : SourceObject

data SourceRole : Set where
  scientificResearchArticle : SourceRole
  patentClaimDisclosure : SourceRole
  independentReplication : SourceRole

data ScientificClaimCategory : Set where
  authorReportedObservation : ScientificClaimCategory
  inventionClaim : ScientificClaimCategory
  externallyReplicatedObservation : ScientificClaimCategory

data HostContext : Set where
  filamentousFungalSystem : HostContext
  yeastSystem : HostContext

data HistoricalLinkKind : Set where
  publicationAcknowledgesProvisional : HistoricalLinkKind
  patentFamilyPriority : HistoricalLinkKind
  sharedGeneralChemistryTopic : HistoricalLinkKind
  independentlyReplicatedSameExperiment : HistoricalLinkKind

data LegalInterpretationKind : Set where
  databaseStatusLabel : LegalInterpretationKind
  jurisdictionSpecificValidityOpinion : LegalInterpretationKind
  freedomToOperateConclusion : LegalInterpretationKind

------------------------------------------------------------------------
-- Source kind does not manufacture a stronger scientific witness.
-- No constructor can build an observed experiment from a patent claim.
------------------------------------------------------------------------

data ObservationAdmission : ScientificClaimCategory → Set where
  admittedAuthorObservation :
    ObservationAdmission authorReportedObservation
  admittedIndependentReplication :
    ObservationAdmission externallyReplicatedObservation

patentClaimNotObservedExperiment :
  ObservationAdmission inventionClaim → NoWitness
patentClaimNotObservedExperiment ()

data ScientificIndependenceAdmission : SourceRole → Set where
  paidIndependentReplication :
    ScientificIndependenceAdmission independentReplication

articleCitationNotReplication :
  ScientificIndependenceAdmission scientificResearchArticle → NoWitness
articleCitationNotReplication ()

patentCitationNotReplication :
  ScientificIndependenceAdmission patentClaimDisclosure → NoWitness
patentCitationNotReplication ()

------------------------------------------------------------------------
-- Different hosts cannot be silently treated as the same experiment.
-- Same chemical family is not an identity of biological context.
------------------------------------------------------------------------

patentHostNotYeastHost :
  filamentousFungalSystem ≡ yeastSystem → NoWitness
patentHostNotYeastHost ()

researchPaperNotPatentPublication :
  researchArticle2014 ≡ patentPublication2015 → NoWitness
researchPaperNotPatentPublication ()

patentPublicationNotYeastStudy :
  patentPublication2015 ≡ yeastArticle2022 → NoWitness
patentPublicationNotYeastStudy ()

yeastPatentNotYeastResearchArticle :
  yeastPatentPublication2023 ≡ yeastArticle2022 → NoWitness
yeastPatentNotYeastResearchArticle ()

data StudyHostRelation : HostContext → HostContext → Set where
  sameFilamentousContext :
    StudyHostRelation filamentousFungalSystem filamentousFungalSystem
  sameYeastContext :
    StudyHostRelation yeastSystem yeastSystem

sharedTopicCannotWeldHost :
  StudyHostRelation filamentousFungalSystem yeastSystem → NoWitness
sharedTopicCannotWeldHost ()

------------------------------------------------------------------------
-- A database state, even one reading "ceased", gives no legal opinion.
------------------------------------------------------------------------

data LegalAdmission : LegalInterpretationKind → Set where
  databaseStateObserved : LegalAdmission databaseStatusLabel

statusLabelNotJurisdictionValidity :
  LegalAdmission jurisdictionSpecificValidityOpinion → NoWitness
statusLabelNotJurisdictionValidity ()

statusLabelNotFreedomToOperate :
  LegalAdmission freedomToOperateConclusion → NoWitness
statusLabelNotFreedomToOperate ()

------------------------------------------------------------------------
-- The patent's disclosure does not prove all 2022 yeast claims.
-- A source-to-source comparison needs its own verified witness.
------------------------------------------------------------------------

data ClaimTransport : SourceObject → SourceObject → Set where
  sameResearchSource :
    ClaimTransport researchArticle2014 researchArticle2014
  samePatentSource :
    ClaimTransport patentPublication2015 patentPublication2015
  sameYeastSource :
    ClaimTransport yeastArticle2022 yeastArticle2022
  sameYeastPatentSource :
    ClaimTransport yeastPatentPublication2023 yeastPatentPublication2023

patentToYeastClaimTransportUnpaid :
  ClaimTransport patentPublication2015 yeastArticle2022 → NoWitness
patentToYeastClaimTransportUnpaid ()

patentToResearchClaimTransportUnpaid :
  ClaimTransport patentPublication2015 researchArticle2014 → NoWitness
patentToResearchClaimTransportUnpaid ()

laterPatentToYeastStudyTransportUnpaid :
  ClaimTransport yeastPatentPublication2023 yeastArticle2022 → NoWitness
laterPatentToYeastStudyTransportUnpaid ()

------------------------------------------------------------------------
-- This proof boundary is intentionally descriptive, not constructive.
-- It has no sequence, reaction, genotype, protocol, or production method.
------------------------------------------------------------------------
