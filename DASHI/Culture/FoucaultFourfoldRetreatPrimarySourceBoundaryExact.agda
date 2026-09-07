module DASHI.Culture.FoucaultFourfoldRetreatPrimarySourceBoundaryExact where

------------------------------------------------------------------------
-- FOUCAULT PRIMARY-SOURCE BOUNDARY FOR FOURFOLD-RETREAT TESTING
--
-- Attribution discipline:
--   Foucault source proposition
--   != later interpretation
--   != DASHI axis appraisal
--   != whole-work doctrine
--   != empirical/historical population law.
--
-- Primary publication carriers and access carriers remain distinct.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source metadata.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryJournalArticle : SourceRole
  primaryBookPassage : SourceRole
  primaryLectureInterview : SourceRole
  accessArchive : SourceRole


record FoucaultSourceReceipt : Set where
  constructor foucault-source-receipt
  field
    upstreamAuthor : String
    title : String
    publicationCarrier : String
    publicationYear : String
    doiOrStableIdentifier : String
    canonicalPublicationLocation : String
    accessLocation : String
    accessCarrierRole : SourceRole
    exactSourceLocation : String
    boundedProposition : String
    dashIInterpretation : String
    wholeDoctrineAuthority : Bool
    namedAxisClosureAuthority : Bool

open FoucaultSourceReceipt public

------------------------------------------------------------------------
-- 1. The Subject and Power (1982).
--
-- Canonical publication metadata is publisher-backed:
-- Critical Inquiry 8(4), 777-795, DOI 10.1086/448181.
------------------------------------------------------------------------

subjectAndPowerReceipt : FoucaultSourceReceipt
subjectAndPowerReceipt =
  foucault-source-receipt
    "Michel Foucault"
    "The Subject and Power"
    "Critical Inquiry 8(4), 777-795"
    "1982"
    "DOI 10.1086/448181"
    "University of Chicago Press / Critical Inquiry"
    "foucault.info/documents/foucault.power/"
    accessArchive
    "section Why Study Power? The Question of the Subject; opening paragraphs"
    "Foucault says the goal of his work was a history of modes by which human beings are made subjects, and explicitly includes the productive/laboring subject in analysis of wealth and economics among those modes of objectification."
    "This supplies direct source evidence that the declared object of analysis is not reducible to discourse alone and includes labour/economic objectification."
    false false

------------------------------------------------------------------------
-- 2. Discipline and Punish, Panopticism.
------------------------------------------------------------------------

disciplineProductionReceipt : FoucaultSourceReceipt
disciplineProductionReceipt =
  foucault-source-receipt
    "Michel Foucault"
    "Discipline and Punish: The Birth of the Prison"
    "Surveiller et punir (Gallimard 1975); English trans. Alan Sheridan, Vintage 1977"
    "1975 / English 1977"
    "book; no DOI asserted here"
    "published book"
    "foucault.info/documents/foucault.disciplineAndPunish.panOpticism/"
    accessArchive
    "Part Three, chapter Panopticism; passage relating apparatus of production, division of labour, disciplinary techniques and capitalist economy"
    "Foucault describes reciprocal relations between production technology, division of labour and disciplinary techniques, and states that growth of a capitalist economy gave rise to the specific modality of disciplinary power."
    "This is primary-source evidence of material, bodily, institutional and production relations inside the analysis."
    false false

------------------------------------------------------------------------
-- 3. Technologies of the Self.
------------------------------------------------------------------------

technologiesPluralityReceipt : FoucaultSourceReceipt
technologiesPluralityReceipt =
  foucault-source-receipt
    "Michel Foucault"
    "Technologies of the Self"
    "seminar/lecture text, later in Technologies of the Self, ed. Martin et al., University of Massachusetts Press"
    "1982 lecture / 1988 publication"
    "book chapter; no DOI asserted here"
    "University of Massachusetts Press publication"
    "foucault.info/documents/foucault.technologiesOfSelf.en/"
    accessArchive
    "Context of Study; enumeration of four major technologies"
    "Foucault distinguishes technologies of production, sign systems, power and the self, and calls each a matrix of practical reason."
    "The source itself uses a plural architecture in which signs are one coordinate among production, power and self-practices."
    false false

------------------------------------------------------------------------
-- 4. Truth/power critique remains source-bounded.
------------------------------------------------------------------------

truthPowerReceipt : FoucaultSourceReceipt
truthPowerReceipt =
  foucault-source-receipt
    "Michel Foucault"
    "Entretien avec Roger-Pol Droit"
    "interview, 1975; later archival reproduction"
    "1975"
    "no DOI asserted here"
    "original interview publication requires separate bibliographic recovery before promotion"
    "foucault.info/documents/foucault.entretien1975.fr/"
    accessArchive
    "passage beginning Le savoir apparaît lié en profondeur..."
    "Foucault links truth-discourse to power effects and asks how those practical and political effects operate."
    "This establishes a critique of truth/power relations, not a source-owned proposition that reason is rejected or that all truth is false."
    false false

------------------------------------------------------------------------
-- Axis-status language deliberately avoids premature Boolean closure.
------------------------------------------------------------------------

data AxisEvidenceStatus : Set where
  directCounterevidenceToSimpleRetreat : AxisEvidenceStatus
  critiquePresentButRetreatUnclosed : AxisEvidenceStatus
  openNeedsBroaderPrimaryCorpus : AxisEvidenceStatus


data FourfoldAxis : Set where
  classAxis : FourfoldAxis
  imperialismAxis : FourfoldAxis
  materialismScienceAxis : FourfoldAxis
  reasonAxis : FourfoldAxis

foucaultAxisStatus : FourfoldAxis → AxisEvidenceStatus
foucaultAxisStatus classAxis = openNeedsBroaderPrimaryCorpus
foucaultAxisStatus imperialismAxis = openNeedsBroaderPrimaryCorpus
foucaultAxisStatus materialismScienceAxis = directCounterevidenceToSimpleRetreat
foucaultAxisStatus reasonAxis = critiquePresentButRetreatUnclosed

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data MaterialInstitutionalAnalysisProvesMarxistMaterialism : Set where
data TruthPowerCritiqueProvesIrrationalism : Set where
data ProductiveSubjectReferenceClosesClassAxis : Set where
data SelectedTextsCloseWholeFoucaultDoctrine : Set where
data AccessArchiveCreatesPrimaryAuthorship : Set where

materialInstitutionalAnalysisDoesNotProveMarxistMaterialism :
  MaterialInstitutionalAnalysisProvesMarxistMaterialism → ⊥
materialInstitutionalAnalysisDoesNotProveMarxistMaterialism ()

truthPowerCritiqueDoesNotProveIrrationalism :
  TruthPowerCritiqueProvesIrrationalism → ⊥
truthPowerCritiqueDoesNotProveIrrationalism ()

productiveSubjectReferenceDoesNotCloseClassAxis :
  ProductiveSubjectReferenceClosesClassAxis → ⊥
productiveSubjectReferenceDoesNotCloseClassAxis ()

selectedTextsDoNotCloseWholeFoucaultDoctrine :
  SelectedTextsCloseWholeFoucaultDoctrine → ⊥
selectedTextsDoNotCloseWholeFoucaultDoctrine ()

accessArchiveDoesNotCreatePrimaryAuthorship :
  AccessArchiveCreatesPrimaryAuthorship → ⊥
accessArchiveDoesNotCreatePrimaryAuthorship ()

record FoucaultFourfoldSourceBoundary : Set where
  constructor foucault-fourfold-source-boundary
  field
    labourEconomicObjectificationRecovered : Bool
    productionDisciplineCapitalRelationRecovered : Bool
    pluralTechnologyArchitectureRecovered : Bool
    truthPowerCritiqueRecovered : Bool
    simpleDiscourseOnlyReadingSupported : Bool
    irrationalismEstablished : Bool
    classRetreatClosed : Bool
    imperialismRetreatClosed : Bool
    materialismRetreatClosedPositive : Bool
    wholeDoctrineClosed : Bool
    strongerAxisClaimsRequireMorePrimarySources : Bool

canonicalFoucaultFourfoldSourceBoundary : FoucaultFourfoldSourceBoundary
canonicalFoucaultFourfoldSourceBoundary =
  foucault-fourfold-source-boundary
    true true true true false false false false false false true
