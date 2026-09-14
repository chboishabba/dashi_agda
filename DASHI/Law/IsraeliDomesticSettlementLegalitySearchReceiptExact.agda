module DASHI.Law.IsraeliDomesticSettlementLegalitySearchReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Law.SensibLawIsraelWestBankOperationalLegalityExact as Israel
import DASHI.Law.SensibLawOperationalLegalityExact as Operational

------------------------------------------------------------------------
-- ISRAELI DOMESTIC SETTLEMENT LEGALITY — BOUNDED SEARCH RECEIPT
--
-- This owner pays a mixed-source acquisition state, not a comprehensive
-- domestic-law conclusion.  Knesset committee language, legislative-process
-- material, an Israeli Government legal-position page, and a Ministry of
-- Justice enforcement self-description are deliberately kept as different
-- source roles.  None is silently promoted into a final court holding,
-- independent audit, or universal proposition about every settlement, outpost,
-- settler act, soldier, ministry, or enforcement event.
------------------------------------------------------------------------

knessetIllegalOutposts2026 : Source.AttributedSource
knessetIllegalOutposts2026 = Source.mkNoDOISource
  "The Knesset — State Control Committee"
  "Subject to new debate, State Control Committee rejects request for State Comptroller's opinion on involvement of government ministries in establishment of illegal outposts in Judea and Samaria"
  "Knesset News"
  "2026"
  "https://m.knesset.gov.il/en/news/pressreleases/pages/press18226t.aspx"
  Source.governmentSource
  "Official Knesset committee-news source using the expression 'illegal settlement outposts' and recording a debate about possible government-ministry involvement. Committee-news language is not a judicial holding and does not determine the legality of every settlement or individual act."
  Source.publicAttribution

knessetSettlementRegulationBill2021 : Source.AttributedSource
knessetSettlementRegulationBill2021 = Source.mkNoDOISource
  "The Knesset"
  "Knesset Plenum passes settlement regulation bill in its preliminary reading"
  "Knesset News"
  "2021"
  "https://main.knesset.gov.il/EN/News/PressReleases/Pages/press11521h.aspx"
  Source.governmentSource
  "Official legislative-process source describing a preliminary-reading bill that proposed regulation procedures, public services/budgeting, and suspension of specified enforcement while regulation proceeded. A preliminary-reading bill is not automatically current enacted law."
  Source.publicAttribution

knessetSettlementRegulationBill2017 : Source.AttributedSource
knessetSettlementRegulationBill2017 = Source.mkNoDOISource
  "The Knesset"
  "Knesset plenum begins debate on settlement regulation bill"
  "Knesset News"
  "2017"
  "https://main.knesset.gov.il/en/News/PressReleases/Pages/Pr13339_pg.aspx"
  Source.governmentSource
  "Official legislative-history source describing a bill intended to retroactively regulate specified settler homes on private Palestinian property. The page is legislative-process evidence, not a comprehensive present-law statement for all settlements or outposts."
  Source.publicAttribution

israeliGovernmentOsloAreaCPosition : Source.AttributedSource
israeliGovernmentOsloAreaCPosition = Source.mkNoDOISource
  "State of Israel — Government of Israel"
  "Palestinian Compliance with the Oslo Accords: A Legal Overview"
  "gov.il"
  "2023"
  "https://www.gov.il/en/pages/oslo06082023"
  Source.governmentSource
  "Official Israeli Government legal-position publication arguing that Oslo allocates governing/planning authority in Area C to Israel and does not itself determine settlements illegal. This is a government legal position, not an independent domestic court adjudication and not a comprehensive legality map for every settlement/outpost/action."
  Source.publicAttribution

ministryJusticeWestBankEnforcement2022 : Source.AttributedSource
ministryJusticeWestBankEnforcement2022 = Source.mkNoDOISource
  "State of Israel — Ministry of Justice, Office of the Deputy Attorney General (International Law)"
  "Israel's Investigation and Prosecution of Ideologically Motivated Offences Against Palestinians in the West Bank"
  "Ministry of Justice"
  "2022"
  "https://www.gov.il/BlobFolder/dynamiccollectorresultitem/hr-0007/he/human-rights-replay_investigation-and-prosecutionof-offences-against-palestinians.pdf"
  Source.governmentSource
  "Official Ministry of Justice self-description of investigation/prosecution policy and claimed enforcement efforts concerning ideologically motivated offences against Palestinians in the West Bank. It pays the existence/content of that government self-description only; it is not an independent audit of enforcement adequacy or proof of any individual case outcome."
  Source.publicAttribution

israeliDomesticSettlementSearchSources : List Source.AttributedSource
israeliDomesticSettlementSearchSources =
  knessetIllegalOutposts2026 ∷
  knessetSettlementRegulationBill2021 ∷
  knessetSettlementRegulationBill2017 ∷
  israeliGovernmentOsloAreaCPosition ∷
  ministryJusticeWestBankEnforcement2022 ∷
  []

israeliDomesticSettlementSearchAtlas : Source.AttributedSourceAtlas
israeliDomesticSettlementSearchAtlas = Source.mkSourceAtlas
  "Israeli domestic settlement-legality bounded search atlas"
  "DASHI.Law.IsraeliDomesticSettlementLegalitySearchReceiptExact"
  israeliDomesticSettlementSearchSources
  "Official Knesset and Israeli Government sources retained by source role. Acquisition pays a mixed domestic-law/legislative/official-position/enforcement-self-description surface, not a comprehensive domestic legality or independent enforcement conclusion."

parentIsraelOperationalLegalityBoundary : Israel.IsraelWestBankOperationalLegalityBoundary
parentIsraelOperationalLegalityBoundary = Israel.canonicalIsraelWestBankOperationalLegalityBoundary

parentOperationalLegalityBoundary : Operational.OperationalLegalityBoundary
parentOperationalLegalityBoundary = Operational.canonicalOperationalLegalityBoundary

record IsraeliDomesticSettlementSearchBoundary : Set where
  constructor israeliDomesticSettlementSearchBoundary
  field
    parentIsraelOperationalLegalityReused : Bool
    parentOperationalLegalityReused : Bool
    officialKnessetIllegalOutpostLanguageLocated : Bool
    knessetRegularisationProposalLocated : Bool
    officialGovernmentOsloAreaCPositionLocated : Bool
    ministryJusticeEnforcementSelfDescriptionLocated : Bool
    comprehensiveDomesticSettlementLegalityPaid : Bool
    everySettlerActionAutomaticallyDomesticLawful : Bool
    everySettlementAutomaticallyDomesticIllegal : Bool
    illegalOutpostLabelAutomaticallyAllSettlementsIllegal : Bool
    legislativeProposalAutomaticallyCurrentLaw : Bool
    knessetCommitteeLanguageAutomaticallyJudicialHolding : Bool
    governmentLegalPositionAutomaticallyIndependentAdjudication : Bool
    ministryEnforcementSelfDescriptionAutomaticallyIndependentAudit : Bool
    areaCPlanningAuthorityAutomaticallyEveryConstructionLawful : Bool
    officialSourceAutomaticallyIndependentAudit : Bool
    domesticLegalityAutomaticallyInternationalLegality : Bool
    sourceSearchAutomaticallyExhaustive : Bool

open IsraeliDomesticSettlementSearchBoundary public

canonicalIsraeliDomesticSettlementSearchBoundary :
  IsraeliDomesticSettlementSearchBoundary
canonicalIsraeliDomesticSettlementSearchBoundary =
  israeliDomesticSettlementSearchBoundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
    false
