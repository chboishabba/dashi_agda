module DASHI.Governance.IndigenousRemovalDelegatedInfrastructureExact where

------------------------------------------------------------------------
-- INDIGENOUS CHILD REMOVAL / DELEGATED INFRASTRUCTURE CASE
--
-- Primary institutional source:
-- Human Rights and Equal Opportunity Commission,
-- "Bringing them home: Report of the National Inquiry into the Separation of
-- Aboriginal and Torres Strait Islander Children from Their Families",
-- April 1997, especially Chapter 19,
-- "Responses of Churches and Other Non-Government Agencies".
-- No DOI asserted for the report.
--
-- Chapter 19 records, inter alia, that churches shared responsibility through
-- provision of accommodation, education, training and work placements; it
-- records church acknowledgements that provision of services enabled removal
-- policies to be implemented and that church welfare services could play a
-- role for the state in keeping children separated from families.  It also
-- treats records, counselling/support and mission/institution land as ongoing
-- responsibility surfaces.
--
-- Additional institutional source:
-- Royal Commission into Institutional Responses to Child Sexual Abuse,
-- Final Report, Volume 16 "Religious institutions" and Volume 13 "Schools",
-- 2017.  No DOI asserted.  Bounded role: institutional-response evidence for
-- religious schools, residential institutions, missions and other settings;
-- not a universal claim about religion or every school.
--
-- The exact dependency/delegation calculus below is a DASHI construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DelegatedEssentialServiceAuthorityExact as Service
import DASHI.Governance.ColonialCarceralDependencyAuthorityBridgeExact as Colonial
import DASHI.Culture.KimmererBraidingAcknowledgement as Braid

record InstitutionalReportReceipt : Set where
  constructor institutionalReportReceipt
  field
    institution : String
    title : String
    date : String
    identifier : String
    boundedRole : String

open InstitutionalReportReceipt public

bringingThemHomeChapter19 : InstitutionalReportReceipt
bringingThemHomeChapter19 = institutionalReportReceipt
  "Human Rights and Equal Opportunity Commission / National Inquiry"
  "Bringing them home: Chapter 19 Responses of Churches and Other Non-Government Agencies"
  "1997"
  "National Inquiry report; no DOI asserted"
  "documents church/non-government participation in accommodation, education, training, work placement, records, counselling and land surfaces associated with forcible removal"

royalCommissionReligiousInstitutions : InstitutionalReportReceipt
royalCommissionReligiousInstitutions = institutionalReportReceipt
  "Royal Commission into Institutional Responses to Child Sexual Abuse"
  "Final Report Volume 16: Religious institutions"
  "2017"
  "Australian Royal Commission final report; no DOI asserted"
  "documents institutional abuse/response evidence across religious schools, orphanages, missions, churches, residential institutions and related settings"

royalCommissionSchools : InstitutionalReportReceipt
royalCommissionSchools = institutionalReportReceipt
  "Royal Commission into Institutional Responses to Child Sexual Abuse"
  "Final Report Volume 13: Schools"
  "2017"
  "Australian Royal Commission final report; no DOI asserted"
  "documents response failures and contributing institutional factors in government and non-government schools"

------------------------------------------------------------------------
-- A non-state institution can form part of an operational state policy without
-- possessing the whole sovereign removal power.
------------------------------------------------------------------------

data InfrastructureRole : Set where
  accommodationRole educationRole trainingRole workPlacementRole : InfrastructureRole
  recordsCustodyRole counsellingRole landInstitutionRole : InfrastructureRole

record DelegatedRemovalInfrastructure : Set where
  constructor delegatedRemovalInfrastructure
  field
    roles : List InfrastructureRole
    sourceReceipts : List InstitutionalReportReceipt
    stateRemovalAuthorityPresent : Bool
    nonStateServiceParticipationPresent : Bool
    nonStateProviderPossessesWholeStateAuthority : Bool
    familySeparationOperationallyEnabled : Bool

open DelegatedRemovalInfrastructure public

bringingThemHomeInfrastructure : DelegatedRemovalInfrastructure
bringingThemHomeInfrastructure = delegatedRemovalInfrastructure
  ( accommodationRole ∷ educationRole ∷ trainingRole ∷ workPlacementRole
  ∷ recordsCustodyRole ∷ counsellingRole ∷ landInstitutionRole ∷ [] )
  (bringingThemHomeChapter19 ∷ [])
  true true false true

------------------------------------------------------------------------
-- Exact semantic separation.
------------------------------------------------------------------------

data ServiceParticipationPromotesSovereignAuthority : Set where

data HistoricalRemovalPromotesAllReligiousCareToRemoval : Set where

data SharedDependencyTopologyPromotesHistoricalIdentity : Set where

serviceParticipationDoesNotPromoteSovereignAuthority :
  ServiceParticipationPromotesSovereignAuthority → ⊥
serviceParticipationDoesNotPromoteSovereignAuthority ()

historicalRemovalDoesNotPromoteAllReligiousCare :
  HistoricalRemovalPromotesAllReligiousCareToRemoval → ⊥
historicalRemovalDoesNotPromoteAllReligiousCare ()

sharedTopologyDoesNotPromoteHistoricalIdentity :
  SharedDependencyTopologyPromotesHistoricalIdentity → ⊥
sharedTopologyDoesNotPromoteHistoricalIdentity ()

------------------------------------------------------------------------
-- Braided provenance: Indigenous/colonial historical evidence remains its own
-- strand with its own warrants.  It is not assimilated into a generic child-
-- religion or carceral model merely because some dependency coordinates can be
-- compared.
------------------------------------------------------------------------

kimmererAcknowledgement : Braid.KimmererBraidingAcknowledgement
kimmererAcknowledgement = Braid.canonicalKimmererBraidingAcknowledgement

colonialComparisonBoundary : Colonial.ColonialCarceralDependencyBoundary
colonialComparisonBoundary = Colonial.canonicalColonialCarceralDependencyBoundary

record IndigenousDelegatedInfrastructureBoundary : Set where
  constructor indigenousDelegatedInfrastructureBoundary
  field
    stateAndNonStateRolesSeparated : Bool
    serviceInfrastructureCanOperationallyEnablePolicy : Bool
    operationalParticipationEqualsWholeLegalAuthority : Bool
    colonialEvidenceFlattenedIntoGenericReligionTheory : Bool
    livingIndigenousKnowledgeClaimedFormalised : Bool
    institutionalCareEvidenceRequiresSourceSpecificity : Bool

canonicalIndigenousDelegatedInfrastructureBoundary :
  IndigenousDelegatedInfrastructureBoundary
canonicalIndigenousDelegatedInfrastructureBoundary =
  indigenousDelegatedInfrastructureBoundary true true false false false true
