module DASHI.Cognition.EpsteinLiquidFundingCrisisLineageBoundary20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LIQUID FUNDING / BEAR STEARNS / CRISIS LINEAGE — 2026-10-14
--
-- This owner pays participation in pre-2008 structured-finance infrastructure
-- and a later Financial Trust -> Bear/JPMorgan-side Class-A-unit exit, while
-- blocking the much stronger claims that Epstein caused the subprime crisis or
-- that a particular federal rescue dollar paid Liquid Funding debt.
------------------------------------------------------------------------

data LiquidFundingSurface : Set where
  chairDirector : LiquidFundingSurface
  bearEquity : LiquidFundingSurface
  bearInvestmentManager : LiquidFundingSurface
  repoTotalReturnSwap : LiquidFundingSurface
  mortgageRelatedCollateral : LiquidFundingSurface
  counterpartyCreditFacility : LiquidFundingSurface
  march2008Replacement : LiquidFundingSurface
  windDown : LiquidFundingSurface
  membershipInterestSale : LiquidFundingSurface
  buyoutSettlement : LiquidFundingSurface
  laterRowanContext : LiquidFundingSurface

record LiquidFundingReceipt : Set where
  constructor liquid-funding-receipt
  field
    label : String
    source : String
    sourceClass : String
    surfaces : List LiquidFundingSurface
    boundedFinding : String
    amountUSD : Nat
    paid : Bool
    crisisCausationPaid : Bool
open LiquidFundingReceipt public

bear2002Disclosure : LiquidFundingReceipt
bear2002Disclosure = liquid-funding-receipt
  "Bear Stearns Liquid Funding disclosure"
  "Bear Stearns FY2002 Form 10-K / Exhibit 13"
  "SEC public-markets filing"
  (bearEquity ∷ bearInvestmentManager ∷ repoTotalReturnSwap ∷ [])
  "Bear Stearns disclosed an approximately 40% equity interest in Liquid Funding Ltd, described as a highly rated special-purpose vehicle participating in repurchase-agreement and total-return-swap markets, with a Bear subsidiary acting as investment manager."
  0 true false

epsteinGovernance : LiquidFundingReceipt
epsteinGovernance = liquid-funding-receipt
  "Epstein Liquid Funding governance role"
  "Liquid Funding offering/corporate records; Paradise Papers/ICIJ lineage"
  "corporate/offshore records"
  (chairDirector ∷ [])
  "Corporate/offering records identify Jeffrey Epstein as director/chairman of Liquid Funding during the vehicle's operating period. Governance status pays a formal role, not unilateral control of every transaction."
  0 true false

mortgageRepoCounterparty : LiquidFundingReceipt
mortgageRepoCounterparty = liquid-funding-receipt
  "Mortgage/CMBS repo counterparty activity"
  "Fieldstone Mortgage Ownership Corp 2006 Form 10-K; JER Investors 2007/2008 SEC filings"
  "SEC counterparty filings"
  (mortgageRelatedCollateral ∷ counterpartyCreditFacility ∷ [])
  "Public counterparties disclose Liquid Funding repo facilities secured by non-prime mortgage-backed securities and CMBS. This places Liquid Funding inside the pre-crisis mortgage/structured-finance plumbing without making it the origin of the housing bubble."
  0 true false

march2008FacilityReplacement : LiquidFundingReceipt
march2008FacilityReplacement = liquid-funding-receipt
  "March 2008 facility replacement"
  "JER Investors Trust 2008 Form 10-K"
  "SEC counterparty filing"
  (march2008Replacement ∷ [])
  "JER Investors states its Liquid Funding repo facility matured on 12 March 2008 and was replaced by a Bear Stearns International facility; after the announced JPMorgan acquisition, JPMorgan guaranteed Bear obligations. The temporal conjunction pays crisis-era transition, not causal responsibility for Bear's collapse."
  0 true false

membershipSaleAgreement2011 : LiquidFundingReceipt
membershipSaleAgreement2011 = liquid-funding-receipt
  "Financial Trust -> Bear Liquid Funding Holdings sale agreement"
  "EFTA00300182..201 / duplicate EFTA00284566"
  "released primary purchase-and-sale agreement"
  (windDown ∷ membershipInterestSale ∷ [])
  "The March 24 2011 Membership Interest Purchase and Sale Agreement identifies Financial Trust Company as seller and Bear Stearns Liquid Funding Holdings Inc as purchaser in a process to acquire Class A Voting Units in Liquid Funding Holdings LLC. The released agreement pays a Financial Trust economic/voting-interest exit object; the exact historical percentage and full cap-table rights require the unit schedules/LLC agreement."
  0 true false

buyoutCredit20110331 : LiquidFundingReceipt
buyoutCredit20110331 = liquid-funding-receipt
  "Liquid Funding Holdings LLC buyout credit"
  "EFTA01510050"
  "JPMorgan/Financial Trust bank-account record"
  (buyoutSettlement ∷ membershipInterestSale ∷ [])
  "A 31 March 2011 Financial Trust bank record shows a USD265,303 book-transfer credit from Bear Stearns Liquid Funding associated with 'LIQUID FUNDING HOLDINGS, LLC BUYOUT'. This pays a settled consideration receipt tied to the 2011 exit. It does not by itself prove that USD265,303 was the entire historical economic value of Financial Trust's Liquid Funding participation."
  265303 true false

releasedWindDownCorpus : LiquidFundingReceipt
releasedWindDownCorpus = liquid-funding-receipt
  "Released Liquid Funding wind-down file inventory"
  "EFTA00300480 / EFTA00300487 / EFTA00299901"
  "released legal-file inventory"
  (windDown ∷ membershipInterestSale ∷ [])
  "Epstein's released legal files inventory distribution/dissolution documents, commercial-paper and liquidity agreements and a 'Liquid Funding Sale of Class A Voting Units' file family. This pays acquisition routing/provenance; unseen schedules remain unpaid."
  0 true false

rowanReintroductionContext : LiquidFundingReceipt
rowanReintroductionContext = liquid-funding-receipt
  "Rowan 2016 re-introduction after Liquid Funding"
  "EFTA02454291 / EFTA02361689"
  "direct email thread"
  (laterRowanContext ∷ [])
  "Marc Rowan later re-introduced Perry Shwachman and Epstein under the subject 'Re-Introduction after Liquid Funding'. The phrase pays Liquid Funding as a prior professional context known to the participants; it does not identify Rowan's exact pre-2008 role without the earlier transaction records."
  0 true false

record CrisisBoundary : Set where
  constructor crisis-boundary
  field
    epsteinFormalLiquidFundingRolePaid : Bool
    bearOwnershipManagementPaid : Bool
    mortgageStructuredFinanceExposurePaid : Bool
    financialTrustVotingEconomicExitPaid : Bool
    buyoutSettlementPaid : Bool
    financialTrustHistoricalPercentagePaid : Bool
    crisisEraWindDownPaid : Bool
    epsteinTriggeredSubprimeCrisis : Bool
    liquidFundingCausedBearCollapse : Bool
    federalRescueSpecificallyPaidLiquidFundingLiabilities : Bool
    march2008ChronologyImpliesCausation : Bool
open CrisisBoundary public

canonicalCrisisBoundary : CrisisBoundary
canonicalCrisisBoundary = crisis-boundary
  true true true true true false true false false false false

data StructuredFinanceRoleImpliesCrisisCause : Set where
data BearEquityImpliesLiquidFundingCausedBearFailure : Set where
data FederalBearRescueImpliesLiquidFundingBailout : Set where
data CrisisChronologyImpliesCausation : Set where
data ExitConsiderationEqualsHistoricalEconomicValue : Set where

structuredFinanceRoleDoesNotCreateCrisisCause : StructuredFinanceRoleImpliesCrisisCause → ⊥
structuredFinanceRoleDoesNotCreateCrisisCause ()

bearEquityDoesNotCreateFailureCause : BearEquityImpliesLiquidFundingCausedBearFailure → ⊥
bearEquityDoesNotCreateFailureCause ()

federalBearRescueDoesNotCreateSpecificLFLBailout : FederalBearRescueImpliesLiquidFundingBailout → ⊥
federalBearRescueDoesNotCreateSpecificLFLBailout ()

crisisChronologyDoesNotCreateCausation : CrisisChronologyImpliesCausation → ⊥
crisisChronologyDoesNotCreateCausation ()

exitConsiderationDoesNotCreateHistoricalValue : ExitConsiderationEqualsHistoricalEconomicValue → ⊥
exitConsiderationDoesNotCreateHistoricalValue ()

------------------------------------------------------------------------
-- Pareto now asks about cap table, risk transfer and successor economics.
------------------------------------------------------------------------

data LiquidFundingDebt : Set where
  exactFinancialTrustEquity : LiquidFundingDebt
  fullOwnershipCapTable : LiquidFundingDebt
  collateralAndLiabilityLedger2007_2008 : LiquidFundingDebt
  april2008LiabilityPayoffSource : LiquidFundingDebt
  jpmorganSuccessorAccounting : LiquidFundingDebt
  unitSaleSchedulesAndAllocation : LiquidFundingDebt
  rowanPriorLiquidFundingRole : LiquidFundingDebt
  realisedGainLossToFinancialTrust : LiquidFundingDebt

record LiquidFundingAcquisition : Set where
  constructor liquid-funding-acquisition
  field
    debt : LiquidFundingDebt
    priority : Nat
    question : String
open LiquidFundingAcquisition public

canonicalLiquidFundingAcquisition : List LiquidFundingAcquisition
canonicalLiquidFundingAcquisition =
  liquid-funding-acquisition fullOwnershipCapTable 100
    "Recover the Liquid Funding Holdings LLC agreement and unit schedules to resolve Bear's direct ~40% interest, Holdings' remainder, Class A voting/economic rights, Financial Trust's exact unit count/percentage, and other holders over time."
  ∷ liquid-funding-acquisition collateralAndLiabilityLedger2007_2008 100
    "Acquire year-end/pre-wind-down asset, repo, commercial-paper and collateral schedules to quantify mortgage/CLO exposure and counterparties at crisis onset."
  ∷ liquid-funding-acquisition april2008LiabilityPayoffSource 100
    "Resolve how the outstanding rated liabilities were satisfied before ratings withdrawal; do not infer Federal Reserve/JPMorgan rescue funding without same-object settlement/accounting records."
  ∷ liquid-funding-acquisition unitSaleSchedulesAndAllocation 99
    "Acquire the 2011 schedules/signature/settlement pages sufficient to map the USD265,303 credit to Financial Trust's exact units and distinguish unit-sale consideration from distributions or wind-down proceeds."
  ∷ liquid-funding-acquisition exactFinancialTrustEquity 99
    "Resolve Financial Trust's exact Class A/voting/economic interest and cost basis rather than inferring percentage from chairmanship or the later buyout receipt."
  ∷ liquid-funding-acquisition jpmorganSuccessorAccounting 99
    "Trace Liquid Funding assets/liabilities/control through JPMorgan's acquisition of Bear and successor entities, using acquisition accounting and legal instruments."
  ∷ liquid-funding-acquisition rowanPriorLiquidFundingRole 98
    "Resolve why Rowan used Liquid Funding as the 2016 re-introduction context: role, transaction, client or professional connection."
  ∷ liquid-funding-acquisition realisedGainLossToFinancialTrust 97
    "Compute Financial Trust realised economics only after cap table, cost basis, distributions and sale/wind-down consideration are paid."
  ∷ []
