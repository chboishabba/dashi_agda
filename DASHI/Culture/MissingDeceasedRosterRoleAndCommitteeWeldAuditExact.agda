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
canonicalRosterRoleAuditBoundary : RosterRoleAuditBoundary
canonicalRosterRoleAuditBoundary = roster-role-audit-boundary false refl false refl false refl false refl
