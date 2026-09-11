module DASHI.Culture.MissingDeceasedRosterRoleAndCommitteeWeldAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data RoleType : Set where
  researchScientist : RoleType
  researchEngineer : RoleType
  technicalProgrammeLeader : RoleType
  administrativeStaff : RoleType
  propertyCustodian : RoleType
  retiredTechnicalOrConstructionStaff : RoleType
  institutionalMember : RoleType
  roleTypeUnresolved : RoleType

data WeldStatus : Set where weldSourceBacked weldPartial weldNotLocated weldContradicted : WeldStatus

record RosterRoleReceipt : Set where
  constructor roster-role-receipt
  field subject : String; roleType : RoleType; roleAtEventTime : WeldStatus; sourceReference : String; boundedReading : String
open RosterRoleReceipt public

record CommitteeCategoryWeld : Set where
  constructor committee-category-weld
  field subject : String; committeeCategory : String; explicitlyNamedByCommittee : Bool; laterReporterNameWeld : WeldStatus; sourceReference : String; boundedReading : String
open CommitteeCategoryWeld public

melissaCasiasRole : RosterRoleReceipt
melissaCasiasRole = roster-role-receipt "Melissa Casias" administrativeStaff weldSourceBacked
  "Los Angeles Times/CBS reporting based on family/law-enforcement records identifies Casias as a LANL administrative assistant at disappearance"
  "LANL affiliation is source-backed, but scientist/researcher status must not be inferred from workplace."

stevenGarciaRole : RosterRoleReceipt
stevenGarciaRole = roster-role-receipt "Steven Garcia" propertyCustodian weldSourceBacked
  "Public reporting identifies Garcia as a contract property custodian connected to the Kansas City National Security Campus"
  "Property/asset custody may be operationally relevant, but it is not a scientific-research role by default."

missingAnthonyChavezRole : RosterRoleReceipt
missingAnthonyChavezRole = roster-role-receipt "Anthony Chavez, missing age 78" retiredTechnicalOrConstructionStaff weldPartial
  "Current reporting describes the missing Chavez as a retired/former LANL construction foreman/employee; no same-person weld to Mark Anthony Chavez's DARHT engineering record is owned"
  "The missing-person row must remain separate from active DARHT/Scorpius engineering unless identity is independently proved."

jasonThomasRole : RosterRoleReceipt
jasonThomasRole = roster-role-receipt "Jason R. Thomas" researchScientist weldSourceBacked
  "Family obituary and NBC/Dateline reporting identify Thomas as a Novartis chemical-biology leader; PubMed supplies matching Novartis chemical-biology research authorship"
  "Scientific/research role and event identity are source-welded; event causation remains separate."

nunoLoureiroRole : RosterRoleReceipt
nunoLoureiroRole = roster-role-receipt "Nuno F. G. Loureiro" technicalProgrammeLeader weldSourceBacked
  "MIT identifies Loureiro as professor, plasma theorist and PSFC director at death"
  "Event-time technical leadership is source-backed."

hicksCommitteeWeld : CommitteeCategoryWeld
hicksCommitteeWeld = committee-category-weld "Michael David Hicks" "explicitly named" true weldSourceBacked
  "House Oversight letter explicitly names Hicks" "No later reporter is needed to establish committee naming."

rezaCommitteeWeld : CommitteeCategoryWeld
rezaCommitteeWeld = committee-category-weld "Monica Reza" "explicitly named" true weldSourceBacked
  "House Oversight letter explicitly names Reza" "Committee naming is closed; the Jacinto patent alias is independently welded by the California DOJ identity record."

mccaslandCommitteeWeld : CommitteeCategoryWeld
mccaslandCommitteeWeld = committee-category-weld "William Neil McCasland" "explicitly named" true weldSourceBacked
  "House Oversight letter explicitly names McCasland" "Committee naming is closed; exact event-time technical portfolio remains open."

jasonCommitteeCategoryWeld : CommitteeCategoryWeld
jasonCommitteeCategoryWeld = committee-category-weld "Jason R. Thomas" "pharmaceutical researcher" false weldPartial
  "Committee letter gives category only; later national reporting identifies Thomas among the cases and his Novartis chemical-biology role fits the category"
  "Later reporting may support a reporter-level category match, but Thomas must not be rewritten as explicitly named by Congress."

loureiroCommitteeCategoryWeld : CommitteeCategoryWeld
loureiroCommitteeCategoryWeld = committee-category-weld "Nuno F. G. Loureiro" "MIT scientist working on nuclear fusion" false weldPartial
  "Committee letter gives category only; later reporting identifies Loureiro and MIT independently establishes his fusion-plasma role"
  "Category fit is strong, but explicit congressional naming is false."

melissaCommitteeCategoryWeld : CommitteeCategoryWeld
melissaCommitteeCategoryWeld = committee-category-weld "Melissa Casias" "one of two people affiliated with LANL" false weldPartial
  "Committee letter supplies LANL category/count only; later reporting identifies Casias as one of the LANL cases"
  "Later reporter/category weld does not transform an administrative role into a scientist role."

missingAnthonyCommitteeCategoryWeld : CommitteeCategoryWeld
missingAnthonyCommitteeCategoryWeld = committee-category-weld "Anthony Chavez, missing age 78" "one of two people affiliated with LANL" false weldPartial
  "Committee letter supplies LANL category/count only; later reporting identifies missing Anthony Chavez as the other LANL case"
  "Category membership remains distinct from Mark Anthony Chavez's engineering publications."

------------------------------------------------------------------------
-- Parallel event-state receipts.
--
-- These are event/case fibres, not scientific-work edges.  They are deliberately
-- kept beside role attribution so ordinary-event evidence and unresolved
-- forensic states can weaken or constrain any common-cause narrative instead of
-- being discarded when they point away from it.
------------------------------------------------------------------------

data EventState : Set where
  missingOpen : EventState
  deceasedCauseKnownMannerUndetermined : EventState
  deceasedOfficialNoFoulPlayPreliminary : EventState
  deceasedChargedLocalCrime : EventState
  deceasedHistoricalBeforeCurrentWindow : EventState
  deceasedPrimaryCauseNotLocated : EventState

record CaseEventReceipt : Set where
  constructor case-event-receipt
  field
    eventSubject : String
    eventState : EventState
    eventDateOrWindow : String
    eventSource : String
    primaryOrOfficialCarrier : Bool
    boundedEventReading : String
    eventImpliesWorkCause : Bool

open CaseEventReceipt public

anthonyChavezMissingEvent : CaseEventReceipt
anthonyChavezMissingEvent = case-event-receipt
  "Anthony Chavez, DOB 1947-01-07"
  missingOpen
  "missing since 2025-05-08, Los Alamos, New Mexico"
  "New Mexico Department of Public Safety missing-person record M99969"
  true
  "Primary state record closes missing-person identity/date/location only; it does not weld this person to Mark Anthony Chavez or the LANL engineering profile."
  false

stevenGarciaMissingEvent : CaseEventReceipt
stevenGarciaMissingEvent = case-event-receipt
  "Steven Abel Garcia, DOB 1977-08-30"
  missingOpen
  "missing since 2025-08-28, Albuquerque, New Mexico"
  "New Mexico Department of Public Safety missing-person record M101688"
  true
  "Primary state record closes missing-person identity/date/location. It does not establish KCNSC employment, clearance scope, asset access or scientific work."
  false

melissaCasiasForensicEvent : CaseEventReceipt
melissaCasiasForensicEvent = case-event-receipt
  "Melissa Casias"
  deceasedCauseKnownMannerUndetermined
  "missing 2025-06-26; remains found 2026-05-28; autopsy reported August 2026"
  "Los Angeles Times 2026-08-18 reporting from New Mexico Office of the Medical Investigator autopsy"
  false
  "Reporting states cause of death was gunshot wound to the head and manner remained undetermined because decomposition limited the examination. Until the primary OMI report is acquired, this remains a secondary report of a primary forensic carrier. Undetermined manner must not be promoted to homicide or suicide."
  false

jasonThomasRecoveryEvent : CaseEventReceipt
jasonThomasRecoveryEvent = case-event-receipt
  "Jason Thomas"
  deceasedOfficialNoFoulPlayPreliminary
  "missing 2025-12-12/13; body recovered 2026-03-17 from Lake Quannapowitt"
  "Middlesex District Attorney / Wakefield Police joint release, 2026-03-17"
  true
  "Official release said clothing preliminarily indicated Jason Thomas and no foul play was suspected; identity and cause/manner were referred to the Chief Medical Examiner. This does not substitute for the final ME determination."
  false

carlGrillmairEvent : CaseEventReceipt
carlGrillmairEvent = case-event-receipt
  "Carl J. Grillmair"
  deceasedChargedLocalCrime
  "killed 2026-02-16; defendant arraigned 2026-05-26"
  "Los Angeles County District Attorney, case 26AVCF00232"
  true
  "The DA alleges a local sequence involving Freddy Snyder, carjacking and a rifle shooting at Grillmair's home. Charges are allegations and the defendant is presumed innocent; the official charging account does not allege a scientific or programme motive."
  false

michaelHicksHistoricalEvent : CaseEventReceipt
michaelHicksHistoricalEvent = case-event-receipt
  "Michael David Hicks"
  deceasedHistoricalBeforeCurrentWindow
  "JPL work ended 2022; died 2023-07-30"
  "AAS Division for Planetary Sciences memorial; University of Arizona LPL memorial; JPL family-news memorial"
  true
  "Institutional/professional memorials agree that Hicks worked at JPL from 1998 through 2022 and died in 2023, so death cannot automatically be treated as an event-time removal from a 2023 JPL role."
  false

matthewSullivanEvent : CaseEventReceipt
matthewSullivanEvent = case-event-receipt
  "Matthew James Sullivan"
  deceasedPrimaryCauseNotLocated
  "died 2024-05-12"
  "Murphy Funeral Homes / Dignity Memorial obituary"
  true
  "The obituary source-backs identity, date and a former USAF intelligence career including NASIC/NSA/AFIA service. It does not state cause/manner of death or independently establish later crash-retrieval/UAP claims."
  false

record RosterRoleAuditBoundary : Set where
  constructor roster-role-audit-boundary
  field
    sensitiveInstitutionImpliesScientistRole : Bool
    sensitiveInstitutionImpliesScientistRoleIsFalse : sensitiveInstitutionImpliesScientistRole ≡ false
    propertyCustodyImpliesScientificResearch : Bool
    propertyCustodyImpliesScientificResearchIsFalse : propertyCustodyImpliesScientificResearch ≡ false
    committeeCategoryImpliesExplicitNaming : Bool
    committeeCategoryImpliesExplicitNamingIsFalse : committeeCategoryImpliesExplicitNaming ≡ false
    laterReporterNameImpliesCommitteePrimaryAttribution : Bool
    laterReporterNameImpliesCommitteePrimaryAttributionIsFalse : laterReporterNameImpliesCommitteePrimaryAttribution ≡ false
    undeterminedMannerImpliesHomicide : Bool
    undeterminedMannerImpliesHomicideIsFalse : undeterminedMannerImpliesHomicide ≡ false
    chargedLocalCrimeImpliesConviction : Bool
    chargedLocalCrimeImpliesConvictionIsFalse : chargedLocalCrimeImpliesConviction ≡ false
    officialNoFoulPlayPreliminaryEqualsFinalME : Bool
    officialNoFoulPlayPreliminaryEqualsFinalMEIsFalse : officialNoFoulPlayPreliminaryEqualsFinalME ≡ false
    eventEvidenceMayWeakenCommonWorkCause : Bool
    eventEvidenceMayWeakenCommonWorkCauseIsTrue : eventEvidenceMayWeakenCommonWorkCause ≡ true

canonicalRosterRoleAuditBoundary : RosterRoleAuditBoundary
canonicalRosterRoleAuditBoundary = roster-role-audit-boundary
  false refl false refl false refl false refl
  false refl false refl false refl true refl
