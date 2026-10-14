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
-- while blocking the much stronger claims that Epstein caused the subprime
-- crisis or that a particular federal rescue dollar paid Liquid Funding debt.
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
  laterSaleDocuments : LiquidFundingSurface
  laterRowanContext : LiquidFundingSurface

record LiquidFundingReceipt : Set where
  constructor liquid-funding-receipt
  field
    label : String
    source : String
    sourceClass : String
    surfaces : List LiquidFundingSurface
    boundedFinding : String
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
  true false

epsteinGovernance : LiquidFundingReceipt
epsteinGovernance = liquid-funding-receipt
  "Epstein Liquid Funding governance role"
  "Liquid Funding offering/corporate records; Paradise Papers/ICIJ lineage"
  "corporate/offshore records"
  (chairDirector ∷ [])
  "Corporate/offering records identify Jeffrey Epstein as director/chairman of Liquid Funding during the vehicle's operating period. Governance status pays a formal role, not unilateral control of every transaction."
  true false

mortgageRepoCounterparty : LiquidFundingReceipt
mortgageRepoCounterparty = liquid-funding-receipt
  "Mortgage/CMBS repo counterparty activity"
  "Fieldstone Mortgage Ownership Corp 2006 Form 10-K; JER Investors 2007/2008 SEC filings"
  "SEC counterparty filings"
  (mortgageRelatedCollateral ∷ counterpartyCreditFacility ∷ [])
  "Public counterparties disclose Liquid Funding repo facilities secured by non-prime mortgage-backed securities and CMBS. This places Liquid Funding inside the pre-crisis mortgage/structured-finance plumbing without making it the origin of the housing bubble."
  true false

march2008FacilityReplacement : LiquidFundingReceipt
march2008FacilityReplacement = liquid-funding-receipt
  "March 2008 facility replacement"
  "JER Investors Trust 2008 Form 10-K"
  "SEC counterparty filing"
  (march2008Replacement ∷ [])
  "JER Investors states its Liquid Funding repo facility matured on 12 March 2008 and was replaced by a Bear Stearns International facility; after the announced JPMorgan acquisition, JPMorgan guaranteed Bear obligations. The temporal conjunction pays crisis-era transition, not causal responsibility for Bear's collapse."
  true false

releasedWindDownCorpus : LiquidFundingReceipt
releasedWindDownCorpus = liquid-funding-receipt
  "Released Liquid Funding wind-down file inventory"
  "EFTA00300480 / EFTA00300487"
  "released legal-file inventory"
  (windDown ∷ laterSaleDocuments ∷ [])
  "Epstein's released legal files inventory Liquid Funding distribution/dissolution documents, commercial-paper and liquidity agreements, a membership-interest purchase/sale agreement, and a signed seller/purchaser document involving Epstein and a Bear Stearns counterparty. The inventory pays existence/provenance; each unseen instrument requires its own terms before promotion."
  true false

rowanReintroductionContext : LiquidFundingReceipt
rowanReintroductionContext = liquid-funding-receipt
  "Rowan 2016 re-introduction after Liquid Funding"
  "EFTA02454291 / EFTA02361689"
  "direct email thread"
  (laterRowanContext ∷ [])
  "Marc Rowan later re-introduced Perry Shwachman and Epstein under the subject 'Re-Introduction after Liquid Funding'. The phrase pays Liquid Funding as a prior professional context known to the participants; it does not identify Rowan's exact pre-2008 role without the earlier transaction records."
  true false

record CrisisBoundary : Set where
  constructor crisis-boundary
  field
    epsteinFormalLiquidFundingRolePaid : Bool
    bearOwnershipManagementPaid : Bool
    mortgageStructuredFinanceExposurePaid : Bool
    crisisEraWindDownPaid : Bool
    epsteinTriggeredSubprimeCrisis : Bool
    liquidFundingCausedBearCollapse : Bool
    federalRescueSpecificallyPaidLiquidFundingLiabilities : Bool
    march2008ChronologyImpliesCausation : Bool
open CrisisBoundary public

canonicalCrisisBoundary : CrisisBoundary
canonicalCrisisBoundary = crisis-boundary
  true true true true false false false false

data StructuredFinanceRoleImpliesCrisisCause : Set where
data BearEquityImpliesLiquidFundingCausedBearFailure : Set where
data FederalBearRescueImpliesLiquidFundingBailout : Set where
data CrisisChronologyImpliesCausation : Set where

structuredFinanceRoleDoesNotCreateCrisisCause : StructuredFinanceRoleImpliesCrisisCause → ⊥
structuredFinanceRoleDoesNotCreateCrisisCause ()

bearEquityDoesNotCreateFailureCause : BearEquityImpliesLiquidFundingCausedBearFailure → ⊥
bearEquityDoesNotCreateFailureCause ()

federalBearRescueDoesNotCreateSpecificLFLBailout : FederalBearRescueImpliesLiquidFundingBailout → ⊥
federalBearRescueDoesNotCreateSpecificLFLBailout ()

crisisChronologyDoesNotCreateCausation : CrisisChronologyImpliesCausation → ⊥
crisisChronologyDoesNotCreateCausation ()

------------------------------------------------------------------------
-- Pareto now asks about ownership, risk transfer and successor economics.
------------------------------------------------------------------------

data LiquidFundingDebt : Set where
  exactFinancialTrustEquity : LiquidFundingDebt
  fullOwnershipCapTable : LiquidFundingDebt
  collateralAndLiabilityLedger2007_2008 : LiquidFundingDebt
  april2008LiabilityPayoffSource : LiquidFundingDebt
  jpmorganSuccessorAccounting : LiquidFundingDebt
  finalMembershipInterestSale : LiquidFundingDebt
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
    "Recover the full voting/economic cap table over time: Bear's ~40%, Liquid Funding Holdings, Financial Trust and other holders; formal chairmanship does not supply ownership percentages."
  ∷ liquid-funding-acquisition collateralAndLiabilityLedger2007_2008 100
    "Acquire year-end/pre-wind-down asset, repo, commercial-paper and collateral schedules to quantify mortgage/CLO exposure and counterparties at crisis onset."
  ∷ liquid-funding-acquisition april2008LiabilityPayoffSource 100
    "Resolve how the outstanding rated liabilities were satisfied before ratings withdrawal; do not infer Federal Reserve/JPMorgan rescue funding without same-object settlement/accounting records."
  ∷ liquid-funding-acquisition exactFinancialTrustEquity 99
    "Resolve Financial Trust's exact Class A/voting/economic interest and cost basis rather than inferring ownership from Epstein's governance role."
  ∷ liquid-funding-acquisition jpmorganSuccessorAccounting 99
    "Trace Liquid Funding assets/liabilities/control through JPMorgan's acquisition of Bear and successor entities, using acquisition accounting and legal instruments."
  ∷ liquid-funding-acquisition finalMembershipInterestSale 98
    "Acquire the executed membership-interest sale/wind-down instruments, consideration and counterparties identified in the released file inventory."
  ∷ liquid-funding-acquisition rowanPriorLiquidFundingRole 98
    "Resolve why Rowan used Liquid Funding as the 2016 re-introduction context: role, transaction, client or professional connection."
  ∷ liquid-funding-acquisition realisedGainLossToFinancialTrust 97
    "Compute Financial Trust/Epstein realised economics only after cap table, contributions, distributions and sale consideration are paid."
  ∷ []
