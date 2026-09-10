module DASHI.Culture.AmyEskridgeCorporateInstitutionalChronologySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeCorporateCustodySurfaceExact as Corporate

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: CORPORATE / INSTITUTIONAL CHRONOLOGY SNOWBALL
--
-- This is an independent OSINT axis from the message/threat chronology.
-- Corporate filings may establish entity identity, office, financing, status,
-- or later dissolution. They do not by themselves establish research purpose,
-- technical IP custody, apparatus custody, motive, or wrongdoing.
------------------------------------------------------------------------

data InstitutionalCarrierClass : Set where
  officialFederalFiling : InstitutionalCarrierClass
  officialStateRegistry : InstitutionalCarrierClass
  officialFederalSpendingRecord : InstitutionalCarrierClass
  secondaryRegistryLead : InstitutionalCarrierClass

data InstitutionalEventClass : Set where
  entityFormation : InstitutionalEventClass
  foreignQualification : InstitutionalEventClass
  officerDirectorRecord : InstitutionalEventClass
  securitiesOffering : InstitutionalEventClass
  payrollReliefLoan : InstitutionalEventClass
  entityStatusObservation : InstitutionalEventClass
  dissolutionEvent : InstitutionalEventClass
  custodyQuestionOpened : InstitutionalEventClass

data EventEntitlement : Set where
  exactPrimaryCarrierInspected : EventEntitlement
  primaryRecordIdentified : EventEntitlement
  secondaryLeadOnly : EventEntitlement

record InstitutionalChronologyAtom : Set where
  constructor institutional-chronology-atom
  field
    eventDate : String
    entityIdentity : String
    eventClass : InstitutionalEventClass
    carrierClass : InstitutionalCarrierClass
    entitlement : EventEntitlement
    sourceLocator : String
    narrowProposition : String
    sameEntityIdentityPaid : Bool
    createsResearchFundingInference : Bool
    createsTechnicalIPCustodyInference : Bool
    createsPostDeathWrongdoingInference : Bool
    createsDeathCausationInference : Bool

open InstitutionalChronologyAtom public

instituteFormationAtom : InstitutionalChronologyAtom
instituteFormationAtom = institutional-chronology-atom
  "2018-10-18"
  "The Institute P.B.C. / Alabama foreign entity 000-549-195"
  entityFormation
  officialStateRegistry
  primaryRecordIdentified
  "Alabama Secretary of State entity 000-549-195; place of formation Delaware"
  "The Alabama registry identifies Delaware formation on 18 October 2018."
  true false false false false

instituteAlabamaQualificationAtom : InstitutionalChronologyAtom
instituteAlabamaQualificationAtom = institutional-chronology-atom
  "2019-04-12"
  "The Institute P.B.C., Inc. / entity 000-549-195"
  foreignQualification
  officialStateRegistry
  primaryRecordIdentified
  "Alabama Secretary of State entity 000-549-195"
  "The foreign corporation qualified in Alabama on 12 April 2019."
  true false false false false

secAmyRoleAndOfferingAtom : InstitutionalChronologyAtom
secAmyRoleAndOfferingAtom = institutional-chronology-atom
  "2019-03-27 filing; first sale 2019-03-12"
  "Institute, P.B.C. / SEC CIK 0001771320"
  securitiesOffering
  officialFederalFiling
  exactPrimaryCarrierInspected
  "SEC Form D accession 0001771320-19-000001"
  "Issuer-filed Form D names Amy Eskridge Pettigrew as president, executive officer and director and reports a $555,000 debt offering with $555,000 sold."
  true false false false false

secAmyOfficerDirectorAtom : InstitutionalChronologyAtom
secAmyOfficerDirectorAtom = institutional-chronology-atom
  "2019-03-27"
  "Institute, P.B.C. / SEC CIK 0001771320"
  officerDirectorRecord
  officialFederalFiling
  exactPrimaryCarrierInspected
  "SEC Form D accession 0001771320-19-000001"
  "The filing records Amy Eskridge Pettigrew as president, executive officer and director; it also names Shantel Butler, Nathan Klose and Samuel Reid as directors."
  true false false false false

pppLoanOneAtom : InstitutionalChronologyAtom
pppLoanOneAtom = institutional-chronology-atom
  "pandemic-relief period; exact award date retained in official award carrier"
  "THE INSTITUTE P.B.C., INC."
  payrollReliefLoan
  officialFederalSpendingRecord
  primaryRecordIdentified
  "USAspending ASST_NON_4113067104_073 / SBA PPP FOIA"
  "Official federal spending data reports a $43,579.20 PPP loan at entity level; the record does not establish Amy as personal recipient or R&D use."
  true false false false false

pppLoanTwoAtom : InstitutionalChronologyAtom
pppLoanTwoAtom = institutional-chronology-atom
  "pandemic-relief period; exact award date retained in official award carrier"
  "THE INSTITUTE PBC"
  payrollReliefLoan
  officialFederalSpendingRecord
  primaryRecordIdentified
  "USAspending ASST_NON_9243538906_073 / SBA PPP FOIA"
  "Official federal spending data reports a $41,351.00 PPP loan at entity level; the record does not establish Amy as personal recipient or R&D use."
  true false false false false

instituteExistsStatusAtom : InstitutionalChronologyAtom
instituteExistsStatusAtom = institutional-chronology-atom
  "public registry observation; exact observation date external to this owner"
  "The Institute P.B.C., Inc. / entity 000-549-195"
  entityStatusObservation
  officialStateRegistry
  primaryRecordIdentified
  "Alabama Secretary of State business entity record"
  "The registry surface reports entity status Exists; status does not establish continuity of research, apparatus, IP, or management."
  true false false false false

holochronDissolutionLeadAtom : InstitutionalChronologyAtom
holochronDissolutionLeadAtom = institutional-chronology-atom
  "2022-12-28"
  "HoloChron LLC / Alabama entity 000-524-283"
  dissolutionEvent
  secondaryRegistryLead
  secondaryLeadOnly
  "OpenCorporates archival record referencing Alabama Secretary of State source"
  "A secondary registry mirror reports HoloChron LLC became dissolved on 28 December 2022; exact Alabama dissolution carrier remains the preferred primary acquisition."
  false false false false false

postDeathCustodyQuestionAtom : InstitutionalChronologyAtom
postDeathCustodyQuestionAtom = institutional-chronology-atom
  "after 2022-06-11"
  "Institute/HoloChron research-property surface"
  custodyQuestionOpened
  secondaryRegistryLead
  secondaryLeadOnly
  "Corporate reverse targets already owned by AmyEskridgeCorporateCustodySurfaceExact"
  "Public corporate changes may justify searching for IP assignment, apparatus location, repository/notebook custody, officer transitions and asset disposition; none is inferred from dissolution or status alone."
  false false false false false

corporateSurfaceStillForbidsPresidentToIPOwnership :
  Corporate.presidentImpliesTechnicalIPOwner Corporate.canonicalEskridgeCorporateCustodyBoundary ≡ false
corporateSurfaceStillForbidsPresidentToIPOwnership = refl

record InstitutionalChronologyBoundary : Set where
  constructor institutional-chronology-boundary
  field
    financingEqualsResearchAward : Bool
    payrollReliefEqualsAntigravityFunding : Bool
    officerTitleEqualsTechnicalIPCustody : Bool
    entityExistsEqualsResearchContinuity : Bool
    postDeathDissolutionEqualsWrongdoing : Bool
    postDeathDissolutionEqualsAssetTransfer : Bool
    corporateChangeEqualsDeathCausation : Bool
    secondaryRegistryLeadMaySeedPrimaryAcquisition : Bool
    independentInstitutionalAxisMayCorroborateOnlyItsOwnNarrowPropositions : Bool

open InstitutionalChronologyBoundary public

canonicalInstitutionalChronologyBoundary : InstitutionalChronologyBoundary
canonicalInstitutionalChronologyBoundary = institutional-chronology-boundary
  false false false false false false false true true
