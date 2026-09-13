module DASHI.Wikimedia.IbrahimSnowballAmyEskridgeClaimLineageClassificationSystemBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact as Claim
import DASHI.Culture.AmyEskridgeApplicationTransformationExact as Amy
import DASHI.Culture.AmyEskridgeAcquisitionProofSearchExact as Acquisition

------------------------------------------------------------------------
-- CONCRETE INVESTIGATIVE CONSUMER
--
-- Ibrahim/Snowball claim-lineage grammar x Amy Eskridge application frontier.
--
-- The public POAMS NASA technical memorandum, the official HAL5 2018
-- presentation/event material, the later captured private-maturation statement,
-- and the still-unidentified Institute derivative object are different source
-- objects.  Acquisition may retain all of them, but payment remains ordered:
-- the first application leaf is still exact private derivative-object identity.
--
-- A second concrete defect also appears here: NASA NTRS Subject Category 70 is
-- a NASA classification coordinate.  It is NOT Dewey Decimal 70 merely because
-- the numeral is the same.  Classification-system identity must snowball with
-- every classification value.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create employment, authorship, same-object continuity, source truth or derivative-object identity")

nasaQid : Identity.ExternalIdentityDemand
nasaQid = mkQid "National Aeronautics and Space Administration" "Q23548"

msfcQid : Identity.ExternalIdentityDemand
msfcQid = mkQid "Marshall Space Flight Center" "Q618696"

amyEskridgeQid : Identity.ExternalIdentityDemand
amyEskridgeQid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "external person identity"
  "Amy Eskridge"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-person Wikidata QID safely promoted in this pass")

instituteForExoticScienceQid : Identity.ExternalIdentityDemand
instituteForExoticScienceQid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "external organization identity"
  "The Institute for Exotic Science"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact organization QID safely promoted in this pass")

holoChronEngineeringQid : Identity.ExternalIdentityDemand
holoChronEngineeringQid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "external organization identity"
  "HoloChron Engineering"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact organization QID safely promoted in this pass")

poamsNtrsIdentifier : Identity.ExternalIdentityDemand
poamsNtrsIdentifier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "official NASA document identity"
  "NASA/TM-20205010911"
  Identity.officialIdentifier
  (Identity.verified "20205010911"
    "NASA NTRS Document ID inspected 2026-09-11")

poamsNtrsCanonicalLink : Identity.ExternalIdentityDemand
poamsNtrsCanonicalLink = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "canonical public-source link"
  "NASA/TM-20205010911 NTRS landing page"
  Identity.canonicalURL
  (Identity.verified "https://ntrs.nasa.gov/citations/20205010911"
    "official NASA NTRS landing page inspected 2026-09-11")

hal5ProgramCanonicalLink : Identity.ExternalIdentityDemand
hal5ProgramCanonicalLink = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "canonical public-source link"
  "HAL5 December 2018 Amy Eskridge program"
  Identity.canonicalURL
  (Identity.verified "https://www.hal5.org/program-2018-12.shtml"
    "official HAL5 program page inspected 2026-09-11")

hal5DeckCanonicalLink : Identity.ExternalIdentityDemand
hal5DeckCanonicalLink = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "canonical public-source link"
  "HAL5 December 2018 Amy Eskridge presentation deck"
  Identity.canonicalURL
  (Identity.verified "https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf"
    "official HAL5-hosted deck inspected 2026-09-11")

privateMaturationStatementCarrier : Identity.ExternalIdentityDemand
privateMaturationStatementCarrier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy Eskridge investigative claim-lineage consumer"
  "exact original-carrier identity"
  "captured 2020 Amy-attributed private-maturation/release-review statement"
  Identity.canonicalURL
  (Identity.unresolved
    "statement existence is retained by the Amy source-stage audit, but exact original carrier/canonical URL is not promoted here")

------------------------------------------------------------------------
-- Dewey / classification-system separation.
------------------------------------------------------------------------

poamsDewey : Dewey.DeweyCoordinate
poamsDewey = Dewey.mkUnresolvedDewey
  "POAMS / NASA technical memorandum subject"
  "NASA NTRS Subject Category 70 is an agency classification, not a Dewey Decimal value; no exact DDC coordinate promoted"

amyApplicationDewey : Dewey.DeweyCoordinate
amyApplicationDewey = Dewey.mkUnresolvedDewey
  "Amy Eskridge Institute application-transformation investigation"
  "consumer spans physics, engineering, history and investigation; no one DDC coordinate promoted"

------------------------------------------------------------------------
-- Primary / official source objects.  No DOI is manufactured where the
-- authoritative public object is identified by a government report number or
-- official institutional URL.
------------------------------------------------------------------------

nasaPoamsTechnicalMemorandumSource : Attribution.AttributedSource
nasaPoamsTechnicalMemorandumSource = Attribution.mkNoDOISource
  "R.H. Eskridge; M.A. Nelson; M.P. Schoenfeld"
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "NASA Technical Memorandum NASA/TM-20205010911; Marshall Space Flight Center"
  "2021"
  "https://ntrs.nasa.gov/citations/20205010911"
  Attribution.governmentSource
  "primary official public carrier for the NASA/MSFC POAMS study and preliminary validation experiment; does not identify Amy Eskridge as an author and does not identify the later Institute private derivative object"
  Attribution.publicAttribution

hal5AmyProgramSource : Attribution.AttributedSource
hal5AmyProgramSource = Attribution.mkNoDOISource
  "Huntsville Alabama L5 Society (HAL5)"
  "December 2018 Program: A Historical Perspective on Anti-Gravity Technology with Amy Eskridge"
  "HAL5 official program page"
  "2018"
  "https://www.hal5.org/program-2018-12.shtml"
  Attribution.institutionalSource
  "primary institutional event/program carrier for Amy Eskridge's public role and presentation; not a private Institute derivative-object identifier or validation record"
  Attribution.publicAttribution

hal5AmyDeckSource : Attribution.AttributedSource
hal5AmyDeckSource = Attribution.mkNoDOISource
  "Amy Eskridge"
  "A Historical Perspective on Anti-Gravity Technology"
  "HAL5-hosted presentation deck"
  "2018"
  "https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf"
  Attribution.practitionerSource
  "primary presentation carrier for the 2018 public historical/organizational surface; does not contain the exact later Institute derivative identity or original Institute experimental dataset"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Existing Amy frontier and generic investigative router are reused.
------------------------------------------------------------------------

amyApplicationFrontier : Amy.AmyApplicationTransformationFrontier
amyApplicationFrontier = Amy.canonicalAmyApplicationTransformationFrontier

amyApplicationSourceAudit : Amy.AmyApplicationSourceStageAudit
amyApplicationSourceAudit = Amy.canonicalAmyApplicationSourceStageAudit

amyAcquisitionBoundary : Acquisition.EskridgeAcquisitionBoundary
amyAcquisitionBoundary = Acquisition.canonicalEskridgeAcquisitionBoundary

investigativeClaimBoundary : Claim.InvestigativeClaimSourceLineageBoundary
investigativeClaimBoundary = Claim.canonicalInvestigativeClaimSourceLineageBoundary

amyDerivativeIdentityRouter : Claim.ClaimResidualRouter
amyDerivativeIdentityRouter = Claim.mkClaimResidualRouter
  "exact Institute privately matured derivative/application object identity"
  "NASA public POAMS foundation + official HAL5 2018 public presentation + retained 2020 Amy-attributed maturation statement"
  "exact derivative title/case or review number/repository identity/apparatus-or-dataset same-object receipt"

------------------------------------------------------------------------
-- Regression 1: identical numeric classification token cannot recover the
-- classification SYSTEM.
------------------------------------------------------------------------

data ClassificationCase : Set where
  nasaSubjectCategory70 deweyDecimal70 : ClassificationCase

data NumericClassificationSurface : Set where sameNumericToken70 : NumericClassificationSurface

data ClassificationSystem : Set where nasaNtrsSubjectSystem deweyDecimalSystem : ClassificationSystem

classificationNumber : ClassificationCase → NumericClassificationSurface
classificationNumber _ = sameNumericToken70

classificationSystem : ClassificationCase → ClassificationSystem
classificationSystem nasaSubjectCategory70 = nasaNtrsSubjectSystem
classificationSystem deweyDecimal70 = deweyDecimalSystem

classificationSystemDefect :
  INF.NonFactorabilityWitness classificationNumber classificationSystem
classificationSystemDefect = INF.nonFactorabilityWitness
  nasaSubjectCategory70 deweyDecimal70 refl (λ ())

sameClassificationNumberCannotFactorClassificationSystem :
  INF.FactorsThrough classificationNumber classificationSystem → ⊥
sameClassificationNumberCannotFactorClassificationSystem =
  INF.witnessRulesOutEveryFlatFactorisation classificationSystemDefect

------------------------------------------------------------------------
-- Regression 2: public POAMS / anti-gravity-adjacent topic surface cannot
-- recover exact private derivative-object identity.
------------------------------------------------------------------------

data ApplicationIdentityCase : Set where
  samePublicTopicDerivativeUnidentified samePublicTopicDerivativeIdentified : ApplicationIdentityCase

data PublicTopicSurface : Set where samePublicApplicationTopic : PublicTopicSurface

data DerivativeIdentityStatus : Set where derivativeIdentityUnpaid derivativeIdentityPaid : DerivativeIdentityStatus

publicTopicSurface : ApplicationIdentityCase → PublicTopicSurface
publicTopicSurface _ = samePublicApplicationTopic

derivativeIdentityStatus : ApplicationIdentityCase → DerivativeIdentityStatus
derivativeIdentityStatus samePublicTopicDerivativeUnidentified = derivativeIdentityUnpaid
derivativeIdentityStatus samePublicTopicDerivativeIdentified = derivativeIdentityPaid

applicationIdentityDefect :
  INF.NonFactorabilityWitness publicTopicSurface derivativeIdentityStatus
applicationIdentityDefect = INF.nonFactorabilityWitness
  samePublicTopicDerivativeUnidentified samePublicTopicDerivativeIdentified refl (λ ())

publicTopicCannotFactorPrivateDerivativeIdentity :
  INF.FactorsThrough publicTopicSurface derivativeIdentityStatus → ⊥
publicTopicCannotFactorPrivateDerivativeIdentity =
  INF.witnessRulesOutEveryFlatFactorisation applicationIdentityDefect

------------------------------------------------------------------------
-- Regression 3: institutional adjacency / common topic cannot recover author or
-- employment identity.  In the official NTRS POAMS record the named authors are
-- R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld; Amy Eskridge is not listed as
-- an author.  HAL5 instead identifies Amy with IES/HoloChron roles.
------------------------------------------------------------------------

data InstitutionalCase : Set where
  sameInstitutionalNeighbourhoodAmy sameInstitutionalNeighbourhoodRH : InstitutionalCase

data InstitutionalSurface : Set where sameNASAInstituteGravityNeighbourhood : InstitutionalSurface

data PersonRoleIdentity : Set where amyInstitutePresenter rhNASAReportAuthor : PersonRoleIdentity

institutionalSurface : InstitutionalCase → InstitutionalSurface
institutionalSurface _ = sameNASAInstituteGravityNeighbourhood

personRoleIdentity : InstitutionalCase → PersonRoleIdentity
personRoleIdentity sameInstitutionalNeighbourhoodAmy = amyInstitutePresenter
personRoleIdentity sameInstitutionalNeighbourhoodRH = rhNASAReportAuthor

institutionPersonDefect :
  INF.NonFactorabilityWitness institutionalSurface personRoleIdentity
institutionPersonDefect = INF.nonFactorabilityWitness
  sameInstitutionalNeighbourhoodAmy sameInstitutionalNeighbourhoodRH refl (λ ())

institutionalAdjacencyCannotFactorPersonRoleIdentity :
  INF.FactorsThrough institutionalSurface personRoleIdentity → ⊥
institutionalAdjacencyCannotFactorPersonRoleIdentity =
  INF.witnessRulesOutEveryFlatFactorisation institutionPersonDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints into Ibrahim parent graph.
------------------------------------------------------------------------

record AmyClaimReverseConstraint : Set where
  constructor amy-claim-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open AmyClaimReverseConstraint public

classificationConstraint : AmyClaimReverseConstraint
classificationConstraint = amy-claim-reverse-constraint
  "Classification / Dewey / institutional subject taxonomies"
  "classification value must retain classification-system identity; equal numerals do not create same classification"
  false

investigationConstraint : AmyClaimReverseConstraint
investigationConstraint = amy-claim-reverse-constraint
  "Investigation / source genealogy"
  "public foundation, public presentation, self-report, exact derivative identity, apparatus/data carrier and successor/handover remain distinct claim-paying objects"
  false

scienceConstraint : AmyClaimReverseConstraint
scienceConstraint = amy-claim-reverse-constraint
  "Science / application transformation"
  "public theory, preliminary experiment, private maturation claim, exact apparatus, calibration, raw/reduced data, validation and uncertainty remain distinct"
  false

identityConstraint : AmyClaimReverseConstraint
identityConstraint = amy-claim-reverse-constraint
  "Person / institution identity"
  "surname, institutional adjacency, family/company relation, authorship, employment and technical responsibility remain separately sourced"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data NasaSubject70IsDewey70 : Set where
data NasaTmIdentifiesPrivateDerivative : Set where
data Hal5PresentationIdentifiesPrivateDerivative : Set where
data SharedSurnameMeansSamePerson : Set where
data NasaAdjacencyMeansNasaEmployment : Set where
data LaterEvidencePaysDerivativeIdentity : Set where
data QidCreatesAuthorship : Set where

aNasaSubjectNumberDoesNotCreateDewey : NasaSubject70IsDewey70 → ⊥
aNasaSubjectNumberDoesNotCreateDewey ()

nasaTmDoesNotIdentifyPrivateDerivative : NasaTmIdentifiesPrivateDerivative → ⊥
nasaTmDoesNotIdentifyPrivateDerivative ()

hal5PresentationDoesNotIdentifyPrivateDerivative : Hal5PresentationIdentifiesPrivateDerivative → ⊥
hal5PresentationDoesNotIdentifyPrivateDerivative ()

sharedSurnameDoesNotCreateSamePerson : SharedSurnameMeansSamePerson → ⊥
sharedSurnameDoesNotCreateSamePerson ()

nasaAdjacencyDoesNotCreateEmployment : NasaAdjacencyMeansNasaEmployment → ⊥
nasaAdjacencyDoesNotCreateEmployment ()

laterEvidenceDoesNotBackPayDerivativeIdentity : LaterEvidencePaysDerivativeIdentity → ⊥
laterEvidenceDoesNotBackPayDerivativeIdentity ()

qidDoesNotCreateAuthorship : QidCreatesAuthorship → ⊥
qidDoesNotCreateAuthorship ()

record AmyIbrahimClaimLineageBoundary : Set where
  constructor amy-ibrahim-claim-lineage-boundary
  field
    genericInvestigativeRouterReused : Bool
    exactAmyApplicationFrontierReused : Bool
    firstUnpaidLeafRemainsDerivativeIdentity : Bool
    nasaAndMsfcQidsAttached : Bool
    amyAndInstituteUnresolvedQidsRetained : Bool
    ntrsOfficialIdentifierAndCanonicalLinkAttached : Bool
    hal5PrimaryCanonicalLinksAttached : Bool
    primarySourceRolesRetained : Bool
    noDoiManufacturedForGovernmentOrInstitutionalPages : Bool
    nasaSubjectTaxonomySeparatedFromDewey : Bool
    publicFoundationSeparatedFromPrivateDerivativeIdentity : Bool
    institutionalAdjacencySeparatedFromPersonRole : Bool
    laterEvidenceMaySnowballWithoutBackPayment : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open AmyIbrahimClaimLineageBoundary public

canonicalAmyIbrahimClaimLineageBoundary : AmyIbrahimClaimLineageBoundary
canonicalAmyIbrahimClaimLineageBoundary =
  amy-ibrahim-claim-lineage-boundary
    true true true true true true true true true true true true true true false
