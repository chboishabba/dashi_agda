module DASHI.Cognition.EpsteinMarcRowanApolloWorkSurface20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MARC ROWAN / EPSTEIN / APOLLO WORK SURFACE — 2026-10-14
--
-- This owner corrects an over-narrow reading of the Dechert statement that
-- Apollo did not retain Epstein. Released records separately pay direct Rowan-
-- Epstein meetings/correspondence and work on Apollo/founder financial/tax
-- questions. A direct work surface does not establish an Apollo corporate
-- retainer, employee/agent status, decision authority or wrongdoing.
------------------------------------------------------------------------

data RowanSurface : Set where
  meeting : RowanSurface
  donorAdvisedFund : RowanSurface
  inversionStructure : RowanSurface
  traValuation : RowanSurface
  historical8865Tax : RowanSurface
  usviInsuranceRegulationIntroduction : RowanSurface
  rothschildBusinessDevelopment : RowanSurface
  thirdPartyIntroduction : RowanSurface

record RowanReceipt : Set where
  constructor rowan-receipt
  field
    label : String
    date : String
    source : String
    sourceClass : String
    surfaces : List RowanSurface
    boundedFinding : String
    directContactPaid : Bool
    substantiveWorkSurfacePaid : Bool
    apolloCorporateRetainerPaid : Bool
open RowanReceipt public

rowanMeetings2013 : RowanReceipt
rowanMeetings2013 = rowan-receipt
  "Rowan-Epstein 2013 meeting schedule"
  "2013-09/10"
  "EFTA00639470; EFTA00384871; EFTA00382067"
  "released schedules/emails"
  (meeting ∷ [])
  "Released scheduling records identify multiple Rowan-Epstein meetings in September/October 2013, including a Black/Rowan/Epstein breakfast. Scheduling pays planned/completed appointments only where the carrier records the appointment as held; it does not establish subject matter by itself."
  true false false

blackRequestsDAFCall2014 : RowanReceipt
blackRequestsDAFCall2014 = rowan-receipt
  "Black directs Rowan/Cohen to call Epstein re donor-advised funds"
  "2014-01-09"
  "EFTA00717483 / EFTA02405147"
  "Apollo executive-assistant email"
  (donorAdvisedFund ∷ [])
  "Leon Black's Apollo executive assistant told Epstein that Black had asked Barry Cohen and Marc Rowan to call him regarding donor-advised funds. This pays a direct requested financial/tax discussion involving Rowan and Epstein, not Apollo retention of Epstein."
  true true false

rowanRothschildInversion201602 : RowanReceipt
rowanRothschildInversion201602 = rowan-receipt
  "Rowan-Epstein Rothschild inversion discussion"
  "2016-02-25"
  "EFTA00833332"
  "direct email thread"
  (inversionStructure ∷ rothschildBusinessDevelopment ∷ [])
  "Rowan and Epstein directly discussed balance-sheet calculations and a possible structure involving Edmond de Rothschild in connection with an inversion; Epstein offered to join a call and Rowan discussed his partner's outreach. This pays substantive financial discussion, not execution of the proposed inversion or an Apollo engagement letter."
  true true false

rowanTRA201603 : RowanReceipt
rowanTRA201603 = rowan-receipt
  "Rowan-Epstein Apollo TRA valuation work"
  "2016-03"
  "EFTA01804071; EFTA02704029; EFTA02340186; EFTA02335969; related EFTA00645429"
  "direct Apollo/Epstein email threads"
  (traValuation ∷ [])
  "Released messages show Rowan and Epstein discussing Apollo tax-receivable-agreement valuation/calculation questions, with Rowan forwarding Apollo valuation-process material and responding to Epstein's calculation questions. This pays a substantive Apollo-related work surface; it does not establish who ultimately adopted any recommendation."
  true true false

wechsler8865Expertise201609 : RowanReceipt
wechsler8865Expertise201609 = rowan-receipt
  "Epstein copied for substantive expertise on historical 8865 project"
  "2016-09-29"
  "EFTA02450093 / duplicate EFTA00816834 lineage"
  "Apollo/family-office email"
  (historical8865Tax ∷ [])
  "Brad Wechsler instructed staff to copy Brad Karp and Jeffrey Epstein on circulated materials and calls concerning historical Form 8865 data for BRH Holdings; he wrote that Epstein was included to obtain the benefit of his substantive expertise. The underlying project involved the family offices/accountants of Black, Harris and Rowan."
  true true false

epstein8865Thinking201608 : RowanReceipt
epstein8865Thinking201608 = rowan-receipt
  "Epstein offers Rowan thinking on 8865 issue"
  "2016-08-26"
  "EFTA02452433"
  "direct email"
  (historical8865Tax ∷ [])
  "Epstein wrote directly to Rowan offering to explain his thinking on the 8865 issue. This corroborates an active tax-work discussion but does not establish that Apollo or Rowan formally retained or paid Epstein for that specific exchange."
  true true false

rowanLiquidFundingReintro201608 : RowanReceipt
rowanLiquidFundingReintro201608 = rowan-receipt
  "Rowan re-introduction after Liquid Funding"
  "2016-08"
  "EFTA02454291 / EFTA02361689"
  "direct email thread"
  (usviInsuranceRegulationIntroduction ∷ thirdPartyIntroduction ∷ [])
  "Rowan re-introduced Sidley Austin partner Perry Shwachman and Epstein under the subject 'Re-Introduction after Liquid Funding' and left them to discuss directly; Shwachman then proposed discussing potential new USVI insurance regulations with Epstein. This pays the introduction and stated subject, not regulatory influence or outcome."
  true true false

rowanRothschildMeeting201601 : RowanReceipt
rowanRothschildMeeting201601 = rowan-receipt
  "Rowan/Imran/Rothschild scheduled at Epstein residence"
  "2016-01-14"
  "EFTA00331035"
  "scheduling email"
  (meeting ∷ rothschildBusinessDevelopment ∷ [])
  "A scheduling email states Rowan and partner Imran would come to Epstein's residence while Ariane de Rothschild and Cynthia Tobiano would also be present. This establishes the arranged meeting configuration; separate reporting disputes whether Epstein himself remained for the meeting, so his physical attendance is not promoted here."
  true false false

record RowanBoundary : Set where
  constructor rowan-boundary
  field
    directRowanEpsteinContactPaid : Bool
    substantiveApolloRelatedWorkSurfacePaid : Bool
    traWorkPaid : Bool
    founder8865WorkPaid : Bool
    rothschildInversionDiscussionPaid : Bool
    usviRegulationIntroductionPaid : Bool
    apolloCorporateRetainerPaid : Bool
    rowanFormalClientOfEpsteinPaid : Bool
    substantiveContactImpliesWrongdoing : Bool
    discussionImpliesImplementedStructure : Bool
open RowanBoundary public

canonicalRowanBoundary : RowanBoundary
canonicalRowanBoundary = rowan-boundary
  true true true true true true false false false false

data WorkSurfaceImpliesCorporateRetainer : Set where
data DiscussionImpliesImplementation : Set where
data IntroductionImpliesRegulatoryInfluence : Set where
data ContactImpliesWrongdoing : Set where

workSurfaceDoesNotCreateCorporateRetainer : WorkSurfaceImpliesCorporateRetainer → ⊥
workSurfaceDoesNotCreateCorporateRetainer ()

discussionDoesNotCreateImplementation : DiscussionImpliesImplementation → ⊥
discussionDoesNotCreateImplementation ()

introductionDoesNotCreateRegulatoryInfluence : IntroductionImpliesRegulatoryInfluence → ⊥
introductionDoesNotCreateRegulatoryInfluence ()

contactDoesNotCreateWrongdoing : ContactImpliesWrongdoing → ⊥
contactDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Current max-cut.
------------------------------------------------------------------------

data RowanDebt : Set where
  traWorkProduct : RowanDebt
  traEconomicBenefit : RowanDebt
  inversionExecution : RowanDebt
  founder8865Deliverables : RowanDebt
  rowanEpsteinCompensation : RowanDebt
  liquidFundingPriorCollaboration : RowanDebt
  usviRegulationOutcome : RowanDebt
  apolloDisclosureReconciliation : RowanDebt

record RowanAcquisition : Set where
  constructor rowan-acquisition
  field
    debt : RowanDebt
    priority : Nat
    question : String
open RowanAcquisition public

canonicalRowanAcquisition : List RowanAcquisition
canonicalRowanAcquisition =
  rowan-acquisition traWorkProduct 100
    "Acquire the TRA worksheets/calculation attachments and identify Epstein's concrete proposed changes rather than treating email consultation as delivered work product."
  ∷ rowan-acquisition founder8865Deliverables 100
    "Acquire Epstein's comments/memos and the final historical 8865 filings or workpapers to determine what his stated substantive expertise changed, if anything."
  ∷ rowan-acquisition rowanEpsteinCompensation 100
    "Search for any payment, fee allocation or Black-family-office accounting that specifically compensates Rowan/Apollo-related work; do not infer it from Black's aggregate fees."
  ∷ rowan-acquisition traEconomicBenefit 99
    "Quantify any realised founder/Apollo economic effect from the TRA work only after tying advice to an adopted calculation or transaction."
  ∷ rowan-acquisition inversionExecution 99
    "Resolve whether the Rothschild/inversion discussions reached an executed structure, were abandoned, or were superseded."
  ∷ rowan-acquisition liquidFundingPriorCollaboration 98
    "Reconstruct the earlier Liquid Funding transaction/working relationship that Rowan invoked in the 2016 re-introduction."
  ∷ rowan-acquisition usviRegulationOutcome 98
    "Trace the proposed USVI insurance-regulation discussion into actual communications, filings or rule changes; introduction and access are not outcome causation."
  ∷ rowan-acquisition apolloDisclosureReconciliation 97
    "Reconcile Apollo's public description of Rowan/Epstein contact against the primary TRA, 8865, inversion, donor-advised-fund and introduction records claim-by-claim."
  ∷ []
