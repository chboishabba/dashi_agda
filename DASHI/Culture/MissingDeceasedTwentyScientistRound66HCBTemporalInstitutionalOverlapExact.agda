module DASHI.Culture.MissingDeceasedTwentyScientistRound66HCBTemporalInstitutionalOverlapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound31MondaloyHCBTemporalContractExact as R31
import DASHI.Culture.MissingDeceasedTwentyScientistRound34McCaslandHCBPublicReferenceExact as R34

------------------------------------------------------------------------
-- ROUND 66: MCCASLAND / HCB TEMPORAL-INSTITUTIONAL OVERLAP
--
-- Primary-source acquisition pays a stronger institutional-temporal overlap:
-- McCasland commanded AFRL from May 2011 to July 2013, while the exact HCB
-- contract/programme FA9300-07-C-0001 had an AFRL Space and Missile Propulsion
-- Division industry-day notice in Aug-Sep 2012.
--
-- This does NOT pay a personal task role, contract-line responsibility,
-- Mondaloy review, funding decision, supervision relation, or direct work with
-- Monica Jacinto/Reza.  Those stronger statements remain derivative/unpaid.
------------------------------------------------------------------------

mccaslandOfficialBiography : Attribution.AttributedSource
mccaslandOfficialBiography = Attribution.mkNoDOISource
  "United States Air Force"
  "Major General William N. McCasland"
  "Air Force Biography Display"
  "2013"
  "https://www.af.mil/About-Us/Biographies/Display/Article/104776/major-general-william-n-mccasland/"
  Attribution.governmentSource
  "Pays McCasland assignment chronology, including Commander, Air Force Research Laboratory, May 2011-July 2013; does not identify HCB/Mondaloy task participation."
  Attribution.publicAttribution

hcbIndustryDayNotice : Attribution.AttributedSource
hcbIndustryDayNotice = Attribution.mkNoDOISource
  "Air Force Research Laboratory / Space and Missile Propulsion Division"
  "Industry Day Briefing on the current status of the Hydrocarbon Boost Engine Technology program"
  "SAM.gov contract opportunity / Special Notice; Notice ID FA9300-07-C-0001"
  "2012"
  "https://sam.gov/opp/d9e3f446b7ed4e0db199b3dd75e405c0/view"
  Attribution.governmentSource
  "Pays that exact HCB programme/contract was active under AFRL Space and Missile Propulsion Division in Aug-Sep 2012; does not identify McCasland personally on the task."
  Attribution.publicAttribution

mccaslandAFRLCommandOverlapPaid : Bool
mccaslandAFRLCommandOverlapPaid = true

hcbExactContractActiveDuringCommandPaid : Bool
hcbExactContractActiveDuringCommandPaid = true

mccaslandHCBInstitutionalTemporalOverlapPaid : Bool
mccaslandHCBInstitutionalTemporalOverlapPaid = true

personalHCBTaskRolePaid : Bool
personalHCBTaskRolePaid = false

personalMondaloyRolePaid : Bool
personalMondaloyRolePaid = false

personalContractLineResponsibilityPaid : Bool
personalContractLineResponsibilityPaid = false

mediaDirectSupervisionClaimPaid : Bool
mediaDirectSupervisionClaimPaid = false

mediaFundingControlClaimPaid : Bool
mediaFundingControlClaimPaid = false

temporalInstitutionalOverlapDoesNotPayExactObject : Bool
temporalInstitutionalOverlapDoesNotPayExactObject = true

commanderOfOrganisationDoesNotImplyEverySubordinateTask : Bool
commanderOfOrganisationDoesNotImplyEverySubordinateTask = true

programmeActiveDuringTenureDoesNotPayPersonalParticipation : Bool
programmeActiveDuringTenureDoesNotPayPersonalParticipation = true

round66H2PaidCount : Nat
round66H2PaidCount = 0

round66H3PaidCount : Nat
round66H3PaidCount = 0

round66Reading : String
round66Reading = "Primary government records now pay a real temporal-institutional overlap: William N. McCasland commanded AFRL from May 2011 to July 2013, and the exact HCB programme/contract FA9300-07-C-0001 was active under AFRL Space and Missile Propulsion Division with a 2012 industry-day notice during that command. This is stronger than mere institution adjacency but remains weaker than personal HCB/Mondaloy task participation. Current media claims that McCasland directly funded, supervised or worked with Reza/Mondaloy are not paid by the acquired primary records. H2 remains unpaid pending an identity-bearing contract/task/review/roster carrier."
