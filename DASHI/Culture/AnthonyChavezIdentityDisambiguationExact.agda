module DASHI.Culture.AnthonyChavezIdentityDisambiguationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ANTHONY CHAVEZ IDENTITY DISAMBIGUATION
--
-- Prevents same-name collapse between the missing Los Alamos resident and the
-- LANL engineer named Mark Anthony Chavez in DARHT/Scorpius technical sources.
------------------------------------------------------------------------

data IdentityStatus : Set where
  identitySourceBacked : IdentityStatus
  identityNotLocated : IdentityStatus
  identityContradicted : IdentityStatus


record PersonIdentitySurface : Set where
  constructor person-identity-surface
  field
    subjectLabel : String
    distinguishingCoordinate : String
    sourceReference : String
    status : IdentityStatus
    boundedReading : String

open PersonIdentitySurface public

missingAnthony : PersonIdentitySurface
missingAnthony = person-identity-surface
  "Anthony Chavez"
  "born 1947-01-07; age 78 when reported missing from Los Alamos in May 2025"
  "New Mexico Department of Public Safety missing-person record M99969; Los Alamos County missing-person release"
  identitySourceBacked
  "This row identifies the missing-person subject only. It does not establish DARHT, Scorpius, accelerator-calibration, or engineering authorship."

markAnthonyEngineer : PersonIdentitySurface
markAnthonyEngineer = person-identity-surface
  "Mark Anthony Chavez"
  "named technical author on DARHT/Scorpius accelerator instrumentation sources"
  "Burris-Mog et al., Rev. Sci. Instrum. 89, 073303 (2018), DOI 10.1063/1.5029837; LA-UR-24-27763"
  identitySourceBacked
  "The technical publications explicitly identify Mark Anthony Chavez. They do not establish identity with the missing Anthony Chavez."

samePersonLink : PersonIdentitySurface
samePersonLink = person-identity-surface
  "Anthony Chavez = Mark Anthony Chavez"
  "same-person identity weld"
  "bounded primary/institutional search"
  identityNotLocated
  "No same-person receipt has been located. Technical roles must not transfer across the name match."

record ChavezIdentityBoundary : Set where
  constructor chavez-identity-boundary
  field
    sameNameImpliesSamePerson : Bool
    sameNameImpliesSamePersonIsFalse : sameNameImpliesSamePerson ≡ false
    sameInstitutionImpliesSamePerson : Bool
    sameInstitutionImpliesSamePersonIsFalse : sameInstitutionImpliesSamePerson ≡ false
    publicationInitialsImpliesRosterIdentity : Bool
    publicationInitialsImpliesRosterIdentityIsFalse : publicationInitialsImpliesRosterIdentity ≡ false
    technicalRoleTransferRequiresIdentityReceipt : Bool
    technicalRoleTransferRequiresIdentityReceiptIsTrue : technicalRoleTransferRequiresIdentityReceipt ≡ true

canonicalChavezIdentityBoundary : ChavezIdentityBoundary
canonicalChavezIdentityBoundary = chavez-identity-boundary
  false refl
  false refl
  false refl
  true refl

data ChavezIdentityReverseTarget : Set where
  acquireFullNameMatch : ChavezIdentityReverseTarget
  acquireDateOfBirthOrPersonnelMatch : ChavezIdentityReverseTarget
  acquireEmploymentHistoryMatch : ChavezIdentityReverseTarget
  acquireContemporaneousBiographyMatch : ChavezIdentityReverseTarget
  acquireInstitutionalIdentityReceipt : ChavezIdentityReverseTarget
