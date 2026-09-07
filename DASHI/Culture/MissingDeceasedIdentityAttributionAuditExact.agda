module DASHI.Culture.MissingDeceasedIdentityAttributionAuditExact where

open import DASHI.Core.Prelude
import DASHI.Core.PersonIdentityAttributionBidiExact as I

------------------------------------------------------------------------
-- ROSTER IDENTITY ATTRIBUTION AUDIT
--
-- Status here concerns same-person attribution only. It does not establish
-- capability criticality, event causation, targeting or homicide.
------------------------------------------------------------------------

amyEskridgeIdentity : I.IdentityReceipt
amyEskridgeIdentity = I.identity-receipt
  "Amy Catherine Eskridge"
  "Amy Eskridge Pettigrew / Amy Eskridge"
  (I.fullLegalOrPublishedName ∷ I.familyOrAlias ∷ I.institution ∷ I.roleTitle ∷ [])
  I.identitySourceBacked
  "SEC Form D for Institute, P.B.C. names Amy Eskridge Pettigrew as President; family/obituary and HAL5 sources identify Amy Catherine Eskridge / Amy Eskridge in the same Huntsville Institute context"
  "The married/legal-name variant is source-welded strongly enough for Institute-role attribution."

frankMaiwaldIdentity : I.IdentityReceipt
frankMaiwaldIdentity = I.identity-receipt
  "Frank Maiwald"
  "Frank W. Maiwald"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.technicalField ∷ [])
  I.identitySourceBacked
  "JPL Principal designation lists Frank W. Maiwald in Planetary Mass Spectrometry; JPL SURP names Frank W. Maiwald as 2023 PI"
  "JPL institutional and project sources provide a strong same-person weld."

nunoLoureiroIdentity : I.IdentityReceipt
nunoLoureiroIdentity = I.identity-receipt
  "Nuno Loureiro"
  "Nuno F. G. Loureiro"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.roleTitle ∷ I.technicalField ∷ [])
  I.identitySourceBacked
  "MIT PSFC/MIT Physics institutional biography and obituary identify Nuno F.G. Loureiro as professor and PSFC director"
  "Institutional full-name, role and field identity are aligned."

michaelHicksIdentity : I.IdentityReceipt
michaelHicksIdentity = I.identity-receipt
  "Michael David Hicks"
  "Michael David Hicks / Michael Hicks"
  (I.fullLegalOrPublishedName ∷ I.dateOrAge ∷ I.institution ∷ I.technicalField ∷ I.education ∷ [])
  I.identitySourceBacked
  "AAS DPS and University of Arizona LPL memorials identify Michael David Hicks, JPL 1998-2022, planetary scientist"
  "Full name, dates, education, institution and research field form a strong weld."

joshuaLeBlancIdentity : I.IdentityReceipt
joshuaLeBlancIdentity = I.identity-receipt
  "Joshua Kyle LeBlanc"
  "Joshua LeBlanc"
  (I.fullLegalOrPublishedName ∷ I.dateOrAge ∷ I.institution ∷ I.technicalField ∷ [])
  I.identitySourceBacked
  "Family obituary identifies Joshua Kyle LeBlanc as a NASA electrical engineer in Huntsville; NASA NTRS names Joshua LeBlanc on FSP I&C work"
  "Name, employer, location and electrical-engineering role support the same-person attribution."

monicaRezaJacintoIdentity : I.IdentityReceipt
monicaRezaJacintoIdentity = I.identity-receipt
  "Monica Reza"
  "Monica A. Jacinto"
  (I.fullLegalOrPublishedName ∷ I.familyOrAlias ∷ I.technicalField ∷ [])
  I.identityPartial
  "Patent record names Monica A. Jacinto as alloy inventor; current public reporting identifies missing Monica Jacinto Reza / Monica Reza and links Jacinto as former/birth name"
  "The alloy inventor and missing-person match is plausible and widely reported, but a primary same-person alias/name-change receipt has not yet been located in this audit."

williamMcCaslandIdentity : I.IdentityReceipt
williamMcCaslandIdentity = I.identity-receipt
  "William Neil McCasland"
  "Neil McCasland / William N. McCasland"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.roleTitle ∷ [])
  I.identitySourceBacked
  "ATA appointment record, Draper annual report and military/institutional biographies use Neil/William Neil/William N. McCasland consistently across the same career history"
  "Name variants are strongly cross-welded by institutional career facts."

jasonThomasIdentity : I.IdentityReceipt
jasonThomasIdentity = I.identity-receipt
  "Jason Thomas"
  "Jason R Thomas"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.technicalField ∷ I.roleTitle ∷ [])
  I.identityPartial
  "Event reporting identifies Jason Thomas as Novartis assistant director of chemical biology; PubMed identifies Jason R Thomas as a Novartis Cambridge chemical-biology author through 2024"
  "Institution and technical field align strongly, but an explicit primary source welding the event subject to the middle-initial publication identity has not yet been located."

carlGrillmairIdentity : I.IdentityReceipt
carlGrillmairIdentity = I.identity-receipt
  "Carl Grillmair"
  "Carl J. Grillmair"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.technicalField ∷ [])
  I.identitySourceBacked
  "IAU/IPAC records and Caltech-linked obituary identify Carl J. Grillmair as the IPAC/Caltech astronomer"
  "Institutional astronomy identity is strongly welded."

anthonyChavezIdentity : I.IdentityReceipt
anthonyChavezIdentity = I.identity-receipt
  "Anthony Chavez, missing age 78 in Los Alamos"
  "Mark Anthony Chavez, LANL DARHT/Scorpius engineer"
  (I.fullLegalOrPublishedName ∷ I.middleNameOrInitial ∷ I.institution ∷ I.roleTitle ∷ [])
  I.identityNotLocated
  "New Mexico missing-person record identifies Anthony Chavez; DARHT/Scorpius technical publications explicitly identify Mark Anthony Chavez"
  "No same-person receipt is owned. Technical capability from Mark Anthony Chavez must not be transferred to the missing Anthony Chavez."

record IdentityAuditBoundary : Set where
  constructor identity-audit-boundary
  field
    allRosterTechnicalEdgesIdentityClosed : Bool
    allRosterTechnicalEdgesIdentityClosedIsFalse : allRosterTechnicalEdgesIdentityClosed ≡ false
    partialIdentityMayBeUsedAsStrongCapabilityWeld : Bool
    partialIdentityMayBeUsedAsStrongCapabilityWeldIsFalse :
      partialIdentityMayBeUsedAsStrongCapabilityWeld ≡ false
    identityAuditPrecedesCriticalityAudit : Bool
    identityAuditPrecedesCriticalityAuditIsTrue : identityAuditPrecedesCriticalityAudit ≡ true

canonicalIdentityAuditBoundary : IdentityAuditBoundary
canonicalIdentityAuditBoundary = identity-audit-boundary false refl false refl true refl
