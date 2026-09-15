module DASHI.Culture.MissingDeceasedTwentyScientistRound32MonicaHCBRolePaymentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Culture.MissingDeceasedTwentyScientistRound31MondaloyHCBTemporalContractExact as R31

------------------------------------------------------------------------
-- ROUND 32: MONICA -> HCB ROLE PAYMENT
--
-- Round 31 paid the contemporaneous HCB contract/programme carrier but left
-- Jacinto/Reza's role on that object unresolved.  The 2016 Engineers Council
-- award programme now supplies a literal role-bearing project surface:
-- "Mondaloy Development for Hydrocarbon Boost Technology Demonstrator",
-- Aerojet Rocketdyne, with Monica A. Jacinto accepting the project award for
-- work maturing Mondaloy 200 for HBTD and AR1.
--
-- This closes the Monica -> HCB object edge.  It still does not name McCasland
-- on HCB, Mondaloy, FA9300-07-C-0001, or that project team.  H2 therefore
-- remains unpaid rather than being inferred from command chronology.
------------------------------------------------------------------------

record MonicaHCBRoleReceipt : Set where
  constructor monica-hcb-role-receipt
  field
    projectAwardSource : Attribution.AttributedSource
    mondaloyPatentSource : Attribution.AttributedSource
    hcbContractSource : Attribution.AttributedSource
    monicaMondaloyInventorPaid : Bool
    mondaloyHCBProjectIdentityPaid : Bool
    monicaHCBProjectRolePaid : Bool
    aerojetProjectIdentityPaid : Bool
    hcbContractCarrierPaid : Bool
    mccaslandCommandOverlapPaid : Bool
    mccaslandHCBPersonalRolePaid : Bool
    crossPersonSameObjectPaid : Bool
    pays : String
    doesNotPay : String
    nextLiteralPayment : String

open MonicaHCBRoleReceipt public

engineersCouncilSource : Attribution.AttributedSource
engineersCouncilSource = Attribution.mkNoDOISource
  "The Engineers' Council"
  "61st Annual Honors and Awards Banquet Program"
  "Engineers Council award programme"
  "2016"
  "https://engineerscouncil.org/ec/Library/Banquet_Programs_Final/UC_Banquet_Program_2016.pdf"
  Attribution.institutionalSource
  "project-award surface titled Mondaloy Development for Hydrocarbon Boost Technology Demonstrator; names Aerojet Rocketdyne, lists project team members, and names Monica A. Jacinto as accepting the project award for maturing Mondaloy 200 for HBTD/AR1"
  Attribution.publicAttribution

engineersCouncilSnowball : Snowball.SourceRoleSnowballReceipt engineersCouncilSource
engineersCouncilSnowball = Snowball.canonicalSourceRoleSnowballReceipt engineersCouncilSource

round32Receipt : MonicaHCBRoleReceipt
round32Receipt = monica-hcb-role-receipt
  engineersCouncilSource
  R31.mondaloyPatentSource
  R31.hcb2012IndustryDaySource
  true
  true
  true
  true
  true
  true
  false
  false
  "Jacinto/Hardwick inventor identity; a literal Aerojet Rocketdyne project named Mondaloy Development for Hydrocarbon Boost Technology Demonstrator; Monica A. Jacinto's named project-award role; and the independently paid FA9300-07-C-0001 HCB carrier during McCasland's command window"
  "McCasland participation in the HCB contract/project, McCasland approval of Mondaloy work, a literal Monica-McCasland same-object role receipt, H2, H3, targeting, or causal linkage"
  "search 2011-2013 FA9300-07-C-0001 modifications, HCB programme reviews, materials-task approval chains, award-fee/performance records, JANNAF/NSMMS proceedings and AFRL leadership briefings for a literal McCasland role or signature on the same HCB/Mondaloy object"

monicaMondaloyInventorPaid : Bool
monicaMondaloyInventorPaid = true

monicaHCBProjectRolePaid : Bool
monicaHCBProjectRolePaid = true

mondaloyHCBProjectIdentityPaid : Bool
mondaloyHCBProjectIdentityPaid = true

mccaslandHCBPersonalRolePaid : Bool
mccaslandHCBPersonalRolePaid = false

crossPersonSameObjectPaid : Bool
crossPersonSameObjectPaid = false

onePersonObjectRoleCannotPayCrossPersonBridge : Bool
onePersonObjectRoleCannotPayCrossPersonBridge = true

commandWindowCannotPayPersonalRole : Bool
commandWindowCannotPayPersonalRole = true

laterAwardCanIdentifyProjectWithoutRetroactivelyNamingCommander : Bool
laterAwardCanIdentifyProjectWithoutRetroactivelyNamingCommander = true

round32H2PaidCount : Nat
round32H2PaidCount = 0

round32H3PaidCount : Nat
round32H3PaidCount = 0

round32Pareto : String
round32Pareto = "Monica -> HCB/Mondaloy is now a source-paid object edge rather than an inferred materials-lineage edge. The sole remaining Reza/McCasland H2 payment is McCasland -> that same HCB/Mondaloy object. Search FA9300-07-C-0001 modifications and programme-review/approval records from 2011-2013, especially materials-tasking, award-fee, leadership-review, JANNAF and NSMMS surfaces. Do not let AFRL command overlap substitute for a named role."