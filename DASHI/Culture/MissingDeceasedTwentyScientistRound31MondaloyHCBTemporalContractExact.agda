module DASHI.Culture.MissingDeceasedTwentyScientistRound31MondaloyHCBTemporalContractExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 31: MONDALOY / HCB TEMPORAL-CONTRACT RESOLUTION
--
-- Search resolves a contemporaneous exact Hydrocarbon Boost contract carrier
-- during McCasland's AFRL command window.  This is materially stronger than a
-- generic same-institution edge: FA9300-07-C-0001 is the Aerojet HBTD contract,
-- a 2012 SAM.gov notice uses the same identifier for an AFRL HCB industry day,
-- and the February-2012 AFRL briefing puts Mondaloy on the HCB roadmap and
-- names AFRL/RX, Aerojet, PWR and Questek on the materials-support surface.
--
-- None of those acquired sources names McCasland as a participant on the HCB
-- contract or names Monica Jacinto on FA9300-07-C-0001.  Temporal overlap and
-- command authority therefore remain separate from a personal same-object role.
------------------------------------------------------------------------

record HCBTemporalContractReceipt : Set where
  constructor hcb-temporal-contract-receipt
  field
    contractAwardSource : Attribution.AttributedSource
    industryDaySource : Attribution.AttributedSource
    fy12BriefingSource : Attribution.AttributedSource
    mondaloyPatentSource : Attribution.AttributedSource
    hcbContractIdentifierPaid : Bool
    aerojetPrimeContractorPaid : Bool
    hcbProgrammeEraPaid : Bool
    mondaloyOnFY12HCBRoadmapPaid : Bool
    materialsSupportIncludesAFRLRXAerojetPaid : Bool
    jacintoHardwickMondaloyInventorIdentityPaid : Bool
    mccaslandCommandTemporalOverlapPaid : Bool
    mccaslandPersonalHCBRolePaid : Bool
    jacintoOnHCBContractPaid : Bool
    sameObjectCrossPersonReceiptPaid : Bool
    pays : String
    doesNotPay : String
    nextLiteralPayment : String

open HCBTemporalContractReceipt public

hcb2007AwardSource : Attribution.AttributedSource
hcb2007AwardSource = Attribution.mkNoDOISource
  "U.S. Department of Defense contract announcement, preserved by GlobalSecurity"
  "Contracts for January 17, 2007 — Aerojet Hydrocarbon Boost Technology Demonstration"
  "DoD contract-announcement reproduction"
  "2007"
  "https://www.globalsecurity.org/military/library/news/2007/01/dod-contracts_3432.htm"
  Attribution.archivalSource
  "acquisition surface paying Aerojet-General as prime on the $109,773,816 HBTD award, contract FA9300-07-C-0001, with work scheduled through October 2015"
  Attribution.publicAttribution

hcb2007AwardSnowball : Snowball.SourceRoleSnowballReceipt hcb2007AwardSource
hcb2007AwardSnowball = Snowball.canonicalSourceRoleSnowballReceipt hcb2007AwardSource

hcb2012IndustryDaySource : Attribution.AttributedSource
hcb2012IndustryDaySource = Attribution.mkNoDOISource
  "U.S. Air Force / SAM.gov"
  "Industry Day Briefing on the current status of the Hydrocarbon Boost Engine Technology program"
  "SAM.gov special notice, FA9300-07-C-0001"
  "2012"
  "https://sam.gov/opp/d9e3f446b7ed4e0db199b3dd75e405c0/view"
  Attribution.governmentSource
  "primary contemporaneous notice paying the exact HCB contract identifier and AFRL Space and Missile Propulsion Division programme status surface in August 2012"
  Attribution.publicAttribution

hcb2012IndustryDaySnowball : Snowball.SourceRoleSnowballReceipt hcb2012IndustryDaySource
hcb2012IndustryDaySnowball = Snowball.canonicalSourceRoleSnowballReceipt hcb2012IndustryDaySource

hcbFY12BriefingSource : Attribution.AttributedSource
hcbFY12BriefingSource = Attribution.mkNoDOISource
  "Richard Cohn, Air Force Research Laboratory"
  "Hydrocarbon Boost Technology for Future Spacelift"
  "AFRL public-release briefing hosted by the National Academies"
  "2012"
  "https://sites.nationalacademies.org/cs/groups/depssite/documents/webpage/deps_068003.pdf"
  Attribution.governmentSource
  "direct public-release AFRL briefing paying the FY12 HCB roadmap, Aerojet prime-contractor identity, Mondaloy materials line, and supporting-materials organisations"
  Attribution.publicAttribution

hcbFY12BriefingSnowball : Snowball.SourceRoleSnowballReceipt hcbFY12BriefingSource
hcbFY12BriefingSnowball = Snowball.canonicalSourceRoleSnowballReceipt hcbFY12BriefingSource

mondaloyPatentSource : Attribution.AttributedSource
mondaloyPatentSource = Attribution.mkNoDOISource
  "Monica A. Jacinto; Dallis Ann Hardwick"
  "Burn-resistant and high tensile strength metal alloys"
  "U.S. patent application US20100266442A1"
  "2010"
  "https://patents.google.com/patent/US20100266442A1/en"
  Attribution.governmentSource
  "patent-record surface paying Jacinto/Hardwick inventor identity for the burn-resistant high-strength alloy lineage later identified as Mondaloy"
  Attribution.publicAttribution

mondaloyPatentSnowball : Snowball.SourceRoleSnowballReceipt mondaloyPatentSource
mondaloyPatentSnowball = Snowball.canonicalSourceRoleSnowballReceipt mondaloyPatentSource

round31Receipt : HCBTemporalContractReceipt
round31Receipt = hcb-temporal-contract-receipt
  hcb2007AwardSource
  hcb2012IndustryDaySource
  hcbFY12BriefingSource
  mondaloyPatentSource
  true
  true
  true
  true
  true
  true
  true
  false
  false
  false
  "FA9300-07-C-0001 as the Aerojet HBTD/HCB contract; HCB active in 2012 during McCasland's AFRL-command chronology; Mondaloy explicitly present on the FY12 HCB roadmap; AFRL/RX, PWR, Aerojet and Questek explicitly present on the HCB materials-support surface; Jacinto/Hardwick inventor identity independently paid"
  "McCasland's personal participation in HCB or Mondaloy, Jacinto's role on FA9300-07-C-0001, a literal Jacinto/Reza-McCasland same-object role receipt, H2, H3, targeting or causal linkage"
  "recover a 2011-2013 HCB contract modification, programme review, materials tasking, briefing attendance/approval chain, JANNAF/NSMMS paper, technical report or roster that literally names McCasland and Jacinto/Reza or their exact Mondaloy work package on FA9300-07-C-0001"

hcbContractIdentifierPaid : Bool
hcbContractIdentifierPaid = true

aerojetPrimeContractorPaid : Bool
aerojetPrimeContractorPaid = true

hcbProgrammeEraPaid : Bool
hcbProgrammeEraPaid = true

mondaloyOnFY12HCBRoadmapPaid : Bool
mondaloyOnFY12HCBRoadmapPaid = true

materialsSupportIncludesAFRLRXAerojetPaid : Bool
materialsSupportIncludesAFRLRXAerojetPaid = true

jacintoHardwickMondaloyInventorIdentityPaid : Bool
jacintoHardwickMondaloyInventorIdentityPaid = true

mccaslandCommandTemporalOverlapPaid : Bool
mccaslandCommandTemporalOverlapPaid = true

mccaslandPersonalHCBRolePaid : Bool
mccaslandPersonalHCBRolePaid = false

jacintoOnHCBContractPaid : Bool
jacintoOnHCBContractPaid = false

sameObjectCrossPersonReceiptPaid : Bool
sameObjectCrossPersonReceiptPaid = false

contemporaneousProgrammeCannotPayPersonalRole : Bool
contemporaneousProgrammeCannotPayPersonalRole = true

commandAuthorityCannotPayTaskParticipation : Bool
commandAuthorityCannotPayTaskParticipation = true

contractIdentityCannotNameUnlistedPerson : Bool
contractIdentityCannotNameUnlistedPerson = true

materialsLineageCannotPayCrossPersonRole : Bool
materialsLineageCannotPayCrossPersonRole = true

round31H2PaidCount : Nat
round31H2PaidCount = 0

round31H3PaidCount : Nat
round31H3PaidCount = 0

round31Pareto : String
round31Pareto = "The Reza/McCasland route has shortened materially: FA9300-07-C-0001 is now the exact contemporaneous HCB contract carrier, and the FY12 AFRL briefing explicitly places Mondaloy and AFRL/RX+Aerojet materials support inside the HCB roadmap during McCasland's command window. The remaining H2 debt is no longer programme chronology; it is a literal personal-role weld. Search 2011-2013 contract modifications, HCB programme reviews, materials tasking, JANNAF/NSMMS proceedings, approval chains and rosters for McCasland plus Jacinto/Reza or the exact Mondaloy work package."