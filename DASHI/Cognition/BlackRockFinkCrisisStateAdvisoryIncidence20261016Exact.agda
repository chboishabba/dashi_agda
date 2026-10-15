module DASHI.Cognition.BlackRockFinkCrisisStateAdvisoryIncidence20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.SystemicLeverageBeneficiaryIncidenceParetoExact as Incidence

------------------------------------------------------------------------
-- BLACKROCK / LARRY FINK / CRISIS-STATE ADVISORY INCIDENCE — 2026-10-16
--
-- This owner fact-checks a circulating compressed narrative about 1980s
-- mortgage securitisation, 2008 TARP/financial-crisis interventions and the
-- 2020 Federal Reserve corporate-credit facilities.
--
-- It preserves the useful systemic claim:
--   private financial expertise can become public crisis infrastructure,
--   while the same firm remains an asset manager/market participant.
--
-- It rejects stronger collapses:
--   adviser/vendor != sovereign decision-maker
--   asset manager AUM != CEO personal ownership
--   CMO != CDO
--   public capital injection != no homeowner programme
--   implementation mandate != policy authorship
--   market exposure != bailout selection causation
------------------------------------------------------------------------

data Surface : Set where
  firstBostonMortgageSecuritisation : Surface
  firstCMOHistory : Surface
  paulsonFinkCrisisContact : Surface
  tarpCapitalPurchaseProgramme : Surface
  maidenLaneAdvisory : Surface
  homeownerRelief : Surface
  fed2020CorporateCredit : Surface
  blackRockClientAssetExposure : Surface
  assetPriceDistribution : Surface

record Receipt : Set where
  constructor receipt
  field
    surface : Surface
    source : String
    sourceClass : String
    boundedFinding : String
    paid : Bool
    decisionAuthorityPaid : Bool
    personalBeneficialOwnershipPaid : Bool
open Receipt public

finkMortgageDesk : Receipt
finkMortgageDesk = receipt
  firstBostonMortgageSecuritisation
  "BlackRock biography / SEC biographical filings"
  "issuer/regulated filing"
  "Before founding BlackRock, Laurence Fink was a First Boston managing director and head/co-head of mortgage and taxable fixed-income businesses. This pays deep mortgage-securitisation expertise, not invention of every later structured-credit product."
  true false false

firstCMOBoundary : Receipt
firstCMOBoundary = receipt
  firstCMOHistory
  "Federal Reserve Bank historical literature on securitisation"
  "central-bank historical research"
  "Freddie Mac issued the first collateralized mortgage obligation in 1983. Fink is widely associated with early private-sector mortgage securitisation/CMO development at First Boston, but 'Larry Fink invented the CDO in 1984' is not the correct object or attribution."
  true false false

paulsonFinkContact : Receipt
paulsonFinkContact = receipt
  paulsonFinkCrisisContact
  "US Treasury Secretary Paulson calendars, September 2008; contemporaneous/retrospective reporting"
  "primary calendar plus secondary reporting"
  "Paulson's September 2008 calendar records crisis-period calls with Larry Fink; reporting describes Fink as advising officials on crisis/TARP structuring. This pays access/advice, not authority to choose recipients or set sovereign policy."
  true false false

tarpNineInstitutions : Receipt
tarpNineInstitutions = receipt
  tarpCapitalPurchaseProgramme
  "US Treasury / Federal Reserve / GAO, October 2008 Capital Purchase Program records"
  "primary government programme record"
  "Treasury initially approved USD125bn of preferred-stock capital purchases for nine major financial institutions within a USD250bn CPP allocation under the larger TARP authority. Treasury, the Federal Reserve and FDIC made programme/systemic-risk decisions; this receipt does not assign recipient selection to BlackRock or Fink."
  true true false

maidenLaneBlackRock : Receipt
maidenLaneBlackRock = receipt
  maidenLaneAdvisory
  "Federal Reserve Bank of New York Maiden Lane records; GAO emergency-assistance review"
  "primary/official programme record"
  "BlackRock Financial Management served as investment manager/adviser on Maiden Lane crisis vehicles, including Bear/AIG asset valuation/management. These were material public-crisis implementation roles with conflict controls, not sovereign bailout-selection authority."
  true false false

homeownerPrograms : Receipt
homeownerPrograms = receipt
  homeownerRelief
  "GAO TARP housing-program reviews"
  "official audit"
  "TARP did fund homeowner/foreclosure-mitigation programmes, including Making Home Affordable and Hardest Hit Fund. They arrived later, were much smaller than system-capital interventions and underperformed initial reach expectations, but 'none went to foreclosure assistance' is false."
  true false false

fed2020BlackRock : Receipt
fed2020BlackRock = receipt
  fed2020CorporateCredit
  "Federal Reserve Bank of New York PMCCF/SMCCF vendor and FAQ records"
  "primary central-bank programme record"
  "In March 2020 the New York Fed retained BlackRock Financial Markets Advisory as investment manager for the corporate credit facilities. BlackRock acted at the sole direction of the New York Fed under Fed investment guidelines; this pays implementation/design support, not unilateral monetary-policy authorship."
  true false false

assetManagerBoundary : Receipt
assetManagerBoundary = receipt
  blackRockClientAssetExposure
  "BlackRock corporate/SEC descriptions of assets under management"
  "issuer/regulated filing"
  "BlackRock manages assets for clients and funds. Assets under management are not Larry Fink's personal assets and should not be described as personal beneficial ownership by the CEO."
  true false false

record CrisisStateBoundary : Set where
  constructor crisis-state-boundary
  field
    finkDeepMortgageExpertisePaid : Bool
    firstCMOWasFreddieMacPaid : Bool
    finkInventedCDOPaid : Bool
    finkAdvisedOfficialsPaid : Bool
    finkChoseNineTARPRecipientsPaid : Bool
    blackRockCrisisImplementationPaid : Bool
    homeownerReliefExistedPaid : Bool
    fed2020BlackRockImplementationPaid : Bool
    blackRockSet2020MonetaryPolicyPaid : Bool
    blackRockAUMEqualsFinkPersonalAssets : Bool
    blackRockExposureToRecipientsRequiresHoldingByHoldingProof : Bool
open CrisisStateBoundary public

canonicalCrisisStateBoundary : CrisisStateBoundary
canonicalCrisisStateBoundary = crisis-state-boundary
  true true false true false true true true false false true

data AdviserImpliesSovereignDecisionAuthority : Set where
data AUMImpliesCEOOwnership : Set where
data CMOHistoryImpliesCDOInvention : Set where
data CrisisContractImpliesRecipientSelection : Set where
data MarketExposureImpliesCrisisAuthorship : Set where

adviserDoesNotCreateSovereignAuthority : AdviserImpliesSovereignDecisionAuthority → ⊥
adviserDoesNotCreateSovereignAuthority ()

aumDoesNotCreateCEOOwnership : AUMImpliesCEOOwnership → ⊥
aumDoesNotCreateCEOOwnership ()

cmoDoesNotCreateCDOInvention : CMOHistoryImpliesCDOInvention → ⊥
cmoDoesNotCreateCDOInvention ()

crisisContractDoesNotCreateRecipientSelection : CrisisContractImpliesRecipientSelection → ⊥
crisisContractDoesNotCreateRecipientSelection ()

marketExposureDoesNotCreateCrisisAuthorship : MarketExposureImpliesCrisisAuthorship → ⊥
marketExposureDoesNotCreateCrisisAuthorship ()

------------------------------------------------------------------------
-- Incidence interpretation.
------------------------------------------------------------------------

crisisStateFirstOrder : Incidence.SystemicLeverageCandidate
crisisStateFirstOrder = Incidence.systemic-leverage-candidate
  "private financial expertise -> crisis-state advisory/implementation"
  Incidence.firstOrder
  Incidence.procurementContracting
  "Which firms received public advisory, valuation, management or implementation mandates during crisis intervention?"
  "Government obtains specialised market/risk capacity; contracted advisers receive fees, privileged implementation position and institutional learning."
  "Taxpayers/public institutions bear programme and counterparty risk; competitors can bear displacement; exact incidence depends on each mandate."
  "Separate sovereign decision authority from adviser/vendor implementation authority."
  "contracts, calendars, programme records, fee schedules, conflicts controls, decision memoranda"
  true false false

crisisStateSecondOrder : Incidence.SystemicLeverageCandidate
crisisStateSecondOrder = Incidence.systemic-leverage-candidate
  "crisis intervention -> asset-holder / incumbent-finance incidence"
  Incidence.secondOrder
  Incidence.distributionalGain
  "How did capital support, liquidity facilities and asset purchases distribute gains/loss avoidance across shareholders, creditors, homeowners, borrowers and public balance sheets?"
  "Stabilised institutions, creditors and diversified asset holders can gain from reduced tail risk and higher asset values; magnitude is instrument- and holder-specific."
  "Foreclosed households, renters, unemployed workers and taxpayers can face distinct burdens; homeowner programmes existed but should be compared quantitatively with financial-sector support."
  "Who owns each claim, who is senior, who receives cash versus mark-to-market benefit, and who can exit?"
  "recipient cap tables, bond/MBS holdings, programme cash flows, HAMP/HHF disbursements, loss and recovery ledgers"
  false false false

crisisStateThirdOrder : Incidence.SystemicLeverageCandidate
crisisStateThirdOrder = Incidence.systemic-leverage-candidate
  "repeated crisis delegation -> durable private-public financial infrastructure"
  Incidence.thirdOrder
  Incidence.institutionalControl
  "Does repeated reliance on the same private financial/risk-management institutions create durable information, modelling, procurement or agenda-setting advantages across crises?"
  "Incumbent advisers/managers can accumulate expertise, relationships and implementation capacity that improve later selection probability."
  "Potential burdens include concentration, conflicts, path dependence and reduced competitive/public capability; none follows automatically from expertise."
  "Distinguish advisory influence, implementation authority, formal decision authority, ownership and beneficiary incidence."
  "2008-2020 contract lineage, procurement competition, staff flows, conflict reviews, model/data ownership, subsequent mandates"
  false false false

------------------------------------------------------------------------
-- Max-cut after fact-checking the compressed narrative.
------------------------------------------------------------------------

data Debt : Set where
  blackRockHoldingsAcrossNineBanks2008 : Debt
  finkTARPAdvicePrimaryDecisionRecord : Debt
  maidenLaneFeeAndConflictIncidence : Debt
  tarpHomeownerVsInstitutionSupportIncidence : Debt
  blackRock2008To2020MandateContinuity : Debt
  fed2020DesignVersusExecutionAuthority : Debt
  assetHolderDistributionByInstrument : Debt

record Acquisition : Set where
  constructor acquisition
  field
    debt : Debt
    priority : Nat
    instruction : String
open Acquisition public

canonicalAcquisition : List Acquisition
canonicalAcquisition =
  acquisition blackRockHoldingsAcrossNineBanks2008 100
    "Resolve BlackRock-managed and Fink-personal beneficial ownership separately for each of the initial nine CPP institutions at the relevant pre/post-announcement dates. Do not turn client AUM into Fink ownership." ∷
  acquisition finkTARPAdvicePrimaryDecisionRecord 100
    "Acquire Paulson/Treasury/Fed memoranda, meeting notes and calendars sufficient to distinguish Fink advice from the actual statutory/regulatory decision chain for CPP/TARP design and recipient selection." ∷
  acquisition tarpHomeownerVsInstitutionSupportIncidence 100
    "Compare bank-capital/liquidity support with homeowner-program obligations, disbursements, reach, timing and foreclosure outcomes on a common incidence ledger." ∷
  acquisition blackRock2008To2020MandateContinuity 99
    "Map BlackRock/FMA public crisis mandates from Bear/AIG/Maiden Lane through later Treasury/Fed work and 2020 CCF implementation, including procurement basis, fees, conflicts and staff flows." ∷
  acquisition maidenLaneFeeAndConflictIncidence 99
    "Quantify BlackRock fees, client-side exposures and conflict-mitigation rules for Maiden Lane/Bear/AIG same-object engagements." ∷
  acquisition fed2020DesignVersusExecutionAuthority 99
    "Separate Federal Reserve/Treasury facility design/eligibility authority from BlackRock implementation and any design consultation using agreements, meeting records and version history." ∷
  acquisition assetHolderDistributionByInstrument 98
    "Measure crisis-policy incidence by security class and beneficial owner rather than using 'asset holders' as one undifferentiated beneficiary class."
  ∷ []
