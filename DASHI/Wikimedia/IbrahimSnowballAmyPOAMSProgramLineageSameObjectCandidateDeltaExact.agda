module DASHI.Wikimedia.IbrahimSnowballAmyPOAMSProgramLineageSameObjectCandidateDeltaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballAmyEskridgeClaimLineageClassificationSystemBidiExact as AmyClaim
import DASHI.Wikimedia.IbrahimSnowballAmyEskridgeArchiveCorporateSameObjectDeltaExact as AmyArchive
import DASHI.Wikimedia.IbrahimSnowballInvestigativeClaimSourceLineageBidiExact as Claim

------------------------------------------------------------------------
-- CONCRETE AMY / POAMS PROGRAMME-LINEAGE DELTA
--
-- NASA primary records narrow the public foundational lineage beyond broad
-- topic adjacency:
--   * SAA8-1519855   = Advanced Propulsion Theory and Experimentation
--   * SAA8-1519855.1 = Advanced Propulsion Theory and Experimentation
--                       POAMS Familiarization
--   * NASA/TM-20205010911 records POAMS work under SAA8-1519855
--   * performing-organization report number M-1531
--
-- This pays an exact PUBLIC programme/report chain.  It does not identify the
-- Institute's privately matured derivative/application object, nor prove that
-- Amy's September-2020 attributed statement refers to M-1531.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "identity inspected 2026-09-11; identity does not create programme participation, same-object continuity, authorship, technical validation or derivative identity")

nasaQid : Identity.ExternalIdentityDemand
nasaQid = AmyClaim.nasaQid

msfcQid : Identity.ExternalIdentityDemand
msfcQid = AmyClaim.msfcQid

quantumMachinesQid : Identity.ExternalIdentityDemand
quantumMachinesQid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "external organization identity"
  "Quantum Machines, LLC (2015 NASA MSFC POAMS agreement counterparty)"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact same-entity Wikidata QID safely promoted; do not confuse with later quantum-control companies sharing the name")

spaceActAgreementQid : Identity.ExternalIdentityDemand
spaceActAgreementQid = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "external legal/institutional instrument identity"
  "NASA Space Act Agreement"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact QID promoted in this pass; individual agreement identifiers remain primary coordinates")

saaBaseIdentifier : Identity.ExternalIdentityDemand
saaBaseIdentifier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "official NASA agreement identifier"
  "Advanced Propulsion Theory and Experimentation"
  Identity.officialIdentifier
  (Identity.verified "SAA8-1519855"
    "NASA active Space Act Agreements list and NASA/TM-20205010911 inspected 2026-09-11")

saaPoamsIdentifier : Identity.ExternalIdentityDemand
saaPoamsIdentifier = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "official NASA agreement identifier"
  "Advanced Propulsion Theory and Experimentation POAMS Familiarization"
  Identity.officialIdentifier
  (Identity.verified "SAA8-1519855.1"
    "NASA active Space Act Agreements list inspected 2026-09-11")

poamsReportNumber : Identity.ExternalIdentityDemand
poamsReportNumber = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "official NASA performing-organization report number"
  "NASA POAMS Technical Memorandum performing-organization report"
  Identity.officialIdentifier
  (Identity.verified "M-1531"
    "NASA NTRS metadata / SF-298 inspected 2026-09-11")

poamsNtrsIdentifier : Identity.ExternalIdentityDemand
poamsNtrsIdentifier = AmyClaim.poamsNtrsIdentifier

poamsNtrsCanonicalLink : Identity.ExternalIdentityDemand
poamsNtrsCanonicalLink = AmyClaim.poamsNtrsCanonicalLink

nasaActiveSaaCanonicalLink : Identity.ExternalIdentityDemand
nasaActiveSaaCanonicalLink = Identity.mkOptionalIdentityDemand
  "Ibrahim/Amy POAMS programme-lineage same-object candidate delta"
  "canonical primary-source link"
  "NASA active Space Act Agreements list containing SAA8-1519855 and SAA8-1519855.1"
  Identity.canonicalURL
  (Identity.verified
    "https://searchpub.nssc.nasa.gov/servlet/sm.web.Fetch/Active%20Domestic%20Private%20Sector%20SAAs%20as%20of%20%2012-31-2016.pdf?did=1848490&rhid=1000&type=released"
    "NASA-hosted primary agreement list inspected 2026-09-11")

------------------------------------------------------------------------
-- Dewey remains navigation-only. NASA agreement/report identifiers are not DDC.
------------------------------------------------------------------------

poamsProgrammeDewey : Dewey.DeweyCoordinate
poamsProgrammeDewey = Dewey.mkUnresolvedDewey
  "NASA MSFC POAMS programme / Space Act Agreement chain"
  "NASA SAA and report identifiers are programme/document coordinates, not Dewey numbers; no exact DDC promoted"

------------------------------------------------------------------------
-- Primary official source objects. No DOI is manufactured.
------------------------------------------------------------------------

nasaSpaceActAgreementListSource : Attribution.AttributedSource
nasaSpaceActAgreementListSource = Attribution.mkNoDOISource
  "National Aeronautics and Space Administration"
  "List of Active Space Act Agreements (as of December 31, 2016) with Domestic Commercial, State Local Government, and Non-profit Partners"
  "NASA Shared Services Center public records"
  "2016"
  "https://searchpub.nssc.nasa.gov/servlet/sm.web.Fetch/Active%20Domestic%20Private%20Sector%20SAAs%20as%20of%20%2012-31-2016.pdf?did=1848490&rhid=1000&type=released"
  Attribution.governmentSource
  "primary institutional source establishing Quantum Machines LLC as MSFC counterparty to SAA8-1519855 Advanced Propulsion Theory and Experimentation (2015-2020) and SAA8-1519855.1 POAMS Familiarization (2015-2017); does not establish any later Institute private derivative"
  Attribution.publicAttribution

nasaPoamsTmSource : Attribution.AttributedSource
nasaPoamsTmSource = AmyClaim.nasaPoamsTechnicalMemorandumSource

------------------------------------------------------------------------
-- The public foundation is now a structured programme/report chain, not merely
-- a broad topic neighbourhood.
------------------------------------------------------------------------

record PublicPOAMSProgrammeChain : Set where
  constructor public-poams-programme-chain
  field
    baseAgreement : String
    poamsAgreement : String
    counterparty : String
    nasaCenter : String
    technicalMemorandumDocumentId : String
    performingOrgReportNumber : String
    ntrsAcquisitionDate : String
    publicationDate : String
    publicDistribution : Bool
open PublicPOAMSProgrammeChain public

canonicalPublicPOAMSProgrammeChain : PublicPOAMSProgrammeChain
canonicalPublicPOAMSProgrammeChain = public-poams-programme-chain
  "SAA8-1519855"
  "SAA8-1519855.1"
  "Quantum Machines, LLC"
  "Marshall Space Flight Center"
  "20205010911"
  "M-1531"
  "2020-12-01"
  "2021-11-01"
  true

------------------------------------------------------------------------
-- Regression 1: exact public programme chain still cannot factor private
-- derivative-object identity.
------------------------------------------------------------------------

data ProgrammeCase : Set where
  samePublicChainDerivativeUnknown samePublicChainDerivativeIdentified : ProgrammeCase

data ProgrammeSurface : Set where samePOAMSProgrammeChain : ProgrammeSurface
data PrivateDerivativeStatus : Set where privateDerivativeUnpaid privateDerivativePaid : PrivateDerivativeStatus

programmeSurface : ProgrammeCase → ProgrammeSurface
programmeSurface _ = samePOAMSProgrammeChain

privateDerivativeStatus : ProgrammeCase → PrivateDerivativeStatus
privateDerivativeStatus samePublicChainDerivativeUnknown = privateDerivativeUnpaid
privateDerivativeStatus samePublicChainDerivativeIdentified = privateDerivativePaid

programmeDerivativeDefect :
  INF.NonFactorabilityWitness programmeSurface privateDerivativeStatus
programmeDerivativeDefect = INF.nonFactorabilityWitness
  samePublicChainDerivativeUnknown samePublicChainDerivativeIdentified refl (λ ())

publicProgrammeChainCannotFactorPrivateDerivativeIdentity :
  INF.FactorsThrough programmeSurface privateDerivativeStatus → ⊥
publicProgrammeChainCannotFactorPrivateDerivativeIdentity =
  INF.witnessRulesOutEveryFlatFactorisation programmeDerivativeDefect

------------------------------------------------------------------------
-- Regression 2: statement description cannot recover the exact NASA object.
-- Amy-attributed 2020 wording supplies: foundational work; one team member;
-- while a civil servant at MSFC; privately matured later; NASA release review.
-- It supplies no title, SAA, M-number, author list, apparatus or dataset ID.
------------------------------------------------------------------------

data StatementCase : Set where
  sameDescriptionIsM1531 sameDescriptionIsOtherNASAObject : StatementCase

data StatementSurface : Set where sameMSFCFoundationalReleaseDescription : StatementSurface
data NASAObjectIdentity : Set where nasaObjectM1531 nasaObjectOther : NASAObjectIdentity

statementSurface : StatementCase → StatementSurface
statementSurface _ = sameMSFCFoundationalReleaseDescription

nasaObjectIdentity : StatementCase → NASAObjectIdentity
nasaObjectIdentity sameDescriptionIsM1531 = nasaObjectM1531
nasaObjectIdentity sameDescriptionIsOtherNASAObject = nasaObjectOther

statementObjectDefect : INF.NonFactorabilityWitness statementSurface nasaObjectIdentity
statementObjectDefect = INF.nonFactorabilityWitness
  sameDescriptionIsM1531 sameDescriptionIsOtherNASAObject refl (λ ())

statementDescriptionCannotFactorExactNASAObject :
  INF.FactorsThrough statementSurface nasaObjectIdentity → ⊥
statementDescriptionCannotFactorExactNASAObject =
  INF.witnessRulesOutEveryFlatFactorisation statementObjectDefect

------------------------------------------------------------------------
-- Regression 3: programme membership cannot recover which team member Amy's
-- statement refers to. The NASA TM names R.H. Eskridge, M.A. Nelson and
-- M.P. Schoenfeld; the statement names no person.
------------------------------------------------------------------------

data TeamMemberCase : Set where
  sameProgrammeMemberRichard sameProgrammeMemberOther : TeamMemberCase

data ProgrammeMemberSurface : Set where sameMSFCTeamMemberDescription : ProgrammeMemberSurface
data NamedPersonStatus : Set where richardEskridgeNamed otherOrUnknownMember : NamedPersonStatus

programmeMemberSurface : TeamMemberCase → ProgrammeMemberSurface
programmeMemberSurface _ = sameMSFCTeamMemberDescription

namedPersonStatus : TeamMemberCase → NamedPersonStatus
namedPersonStatus sameProgrammeMemberRichard = richardEskridgeNamed
namedPersonStatus sameProgrammeMemberOther = otherOrUnknownMember

teamMemberIdentityDefect :
  INF.NonFactorabilityWitness programmeMemberSurface namedPersonStatus
teamMemberIdentityDefect = INF.nonFactorabilityWitness
  sameProgrammeMemberRichard sameProgrammeMemberOther refl (λ ())

teamMemberDescriptionCannotFactorPersonIdentity :
  INF.FactorsThrough programmeMemberSurface namedPersonStatus → ⊥
teamMemberDescriptionCannotFactorPersonIdentity =
  INF.witnessRulesOutEveryFlatFactorisation teamMemberIdentityDefect

------------------------------------------------------------------------
-- Ordered investigation routing: evidence strength improves without back-paying
-- the first unpaid leaf.
------------------------------------------------------------------------

priorArchiveBoundary : AmyArchive.AmyArchiveCorporateSameObjectBoundary
priorArchiveBoundary = AmyArchive.canonicalAmyArchiveCorporateSameObjectBoundary

programmeLineageRouter : Claim.ClaimResidualRouter
programmeLineageRouter = Claim.mkClaimResidualRouter
  "whether Amy's September-2020 attributed foundational-work statement refers to NASA POAMS programme/report M-1531 and whether the Institute private maturation is its exact derivative"
  "exact NASA SAA8-1519855 / SAA8-1519855.1 programme chain + NASA/TM-20205010911 / M-1531 + December-2020 NTRS acquisition + September-2020 attributed statement"
  "explicit title/SAA/M-1531 cross-reference in the original Amy carrier; NASA release/DAA/EDAA/NF-1676 routing object tying the statement to M-1531; or apparatus/dataset/version same-object receipt bridging public NASA and private Institute work"

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record ProgrammeLineageReverseConstraint : Set where
  constructor programme-lineage-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open ProgrammeLineageReverseConstraint public

programmeConstraint : ProgrammeLineageReverseConstraint
programmeConstraint = programme-lineage-reverse-constraint
  "Programme / project / publication"
  "agreement identity, task/sub-agreement identity, counterparty, performing organization, report number, document ID, acquisition date and publication date remain separately attributable"
  false

sameObjectConstraint : ProgrammeLineageReverseConstraint
sameObjectConstraint = programme-lineage-reverse-constraint
  "Investigation / same-object continuity"
  "exact shared programme lineage upgrades a candidate but does not replace an explicit cross-reference, release-routing receipt or apparatus/data same-object witness"
  false

attributionConstraint : ProgrammeLineageReverseConstraint
attributionConstraint = programme-lineage-reverse-constraint
  "Attribution / person identity"
  "team-member description, authorship, civil-service timing, later private affiliation and family/institution adjacency remain distinct"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data SameSAAChainMeansPrivateDerivative : Set where
data ReleaseTimingMeansSamePaper : Set where
data TeamMemberMeansRichardEskridge : Set where
data M1531MeansInstituteDerivative : Set where
data AgreementCounterpartyMeansInstitute : Set where
data QidCreatesProgrammeParticipation : Set where

sameSaaChainDoesNotCreatePrivateDerivative : SameSAAChainMeansPrivateDerivative → ⊥
sameSaaChainDoesNotCreatePrivateDerivative ()

releaseTimingDoesNotCreateSamePaper : ReleaseTimingMeansSamePaper → ⊥
releaseTimingDoesNotCreateSamePaper ()

teamMemberDoesNotMeanRichardEskridge : TeamMemberMeansRichardEskridge → ⊥
teamMemberDoesNotMeanRichardEskridge ()

m1531DoesNotCreateInstituteDerivative : M1531MeansInstituteDerivative → ⊥
m1531DoesNotCreateInstituteDerivative ()

agreementCounterpartyDoesNotBecomeInstitute : AgreementCounterpartyMeansInstitute → ⊥
agreementCounterpartyDoesNotBecomeInstitute ()

qidDoesNotCreateProgrammeParticipation : QidCreatesProgrammeParticipation → ⊥
qidDoesNotCreateProgrammeParticipation ()

record AmyPOAMSProgrammeLineageBoundary : Set where
  constructor amy-poams-programme-lineage-boundary
  field
    nasaAndMsfcQidsReused : Bool
    quantumMachinesAndSpaceActQidsUnresolvedExplicitly : Bool
    saaIdentifiersAttached : Bool
    m1531ReportNumberAttached : Bool
    ntrsDocumentIdAndCanonicalLinkAttached : Bool
    nasaPrimarySaaListAttached : Bool
    governmentSourcesCarryNoManufacturedDoi : Bool
    deweySeparatedFromProgrammeIdentifiers : Bool
    publicFoundationUpgradedToExactProgrammeChain : Bool
    programmeChainSeparatedFromPrivateDerivativeIdentity : Bool
    statementDescriptionSeparatedFromExactNASAObject : Bool
    teamMemberDescriptionSeparatedFromPersonIdentity : Bool
    firstUnpaidLeafRemainsExactPrivateDerivativeIdentity : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open AmyPOAMSProgrammeLineageBoundary public

canonicalAmyPOAMSProgrammeLineageBoundary : AmyPOAMSProgrammeLineageBoundary
canonicalAmyPOAMSProgrammeLineageBoundary =
  amy-poams-programme-lineage-boundary
    true true true true true true true true true true true true true true false
