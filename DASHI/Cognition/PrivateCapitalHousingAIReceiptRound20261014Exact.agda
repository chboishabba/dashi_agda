module DASHI.Cognition.PrivateCapitalHousingAIReceiptRound20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PrivateCapitalHousingAIInfrastructureCrossPollinationExact as Cross

------------------------------------------------------------------------
-- PRIVATE-CAPITAL HOUSING / AI / POWER RECEIPT ROUND — 2026-10-14
------------------------------------------------------------------------

data InstrumentKind : Set where
  platformAcquisition : InstrumentKind
  mortgagePortfolioFinance : InstrumentKind
  computeCapitalPlatform : InstrumentKind
  computeFinancingMOU : InstrumentKind
  powerProjectEquity : InstrumentKind
  listedEquityExposure : InstrumentKind

record TransactionReceipt : Set where
  constructor transaction-receipt
  field
    label : String
    source : String
    instrument : InstrumentKind
    boundedFinding : String
    amountOrScale : String
    paid : Bool
open TransactionReceipt public

apolloGatehouseHousing : TransactionReceipt
apolloGatehouseHousing = transaction-receipt
  "Apollo Gatehouse Living Group"
  "Apollo press release, 1 April 2026"
  platformAcquisition
  "Apollo-managed funds acquired Gatehouse Living Group, a vertically integrated UK residential investment/management platform. Gatehouse states it had acquired more than 5,000 new-build single-family rental homes from housebuilders and its Ascend arm manages more than 10,000 homes for itself and third parties."
  ">5,000 acquired homes; >10,000 managed homes"
  true

blackstoneHSBCAustraliaMortgages : TransactionReceipt
blackstoneHSBCAustraliaMortgages = transaction-receipt
  "Blackstone HSBC Australia home-loan portfolio"
  "Blackstone press release, 31 July 2026"
  mortgagePortfolioFinance
  "Blackstone Credit & Insurance, Tactical Opportunities and Real Estate Debt Strategies signed a definitive agreement to finance the acquisition of HSBC's Australian home-loan portfolio. This is mortgage-credit exposure, not fee-simple acquisition of the underlying houses."
  "AUD 36 billion / USD 25 billion portfolio"
  true

apolloBlackstoneXPV : TransactionReceipt
apolloBlackstoneXPV = transaction-receipt
  "Apollo/Blackstone Broadcom AI XPV platform"
  "Apollo/Broadcom/Blackstone announcements, 9 June 2026"
  computeCapitalPlatform
  "Apollo leads, with Blackstone and global banks, an initial AI-compute capital solution for Broadcom's XPV platform. The platform is designed for more than 20 GW through 2028 and the first tranche supports Anthropic compute on Fluidstack sites."
  "USD 35 billion initial capital solution; >20 GW platform target"
  true

nvidiaComputeFinancingPlatforms : TransactionReceipt
nvidiaComputeFinancingPlatforms = transaction-receipt
  "NVIDIA institutional compute-financing platforms"
  "NVIDIA press release, 10 August 2026"
  computeFinancingMOU
  "NVIDIA announced strategic financing-platform partnerships with Apollo, BlackRock, Blackstone, Brookfield, Goldman Sachs and KKR intended to turn NVIDIA compute/full-stack AI infrastructure into a financed investable asset class with long-duration usage-linked revenue."
  ">USD 500 billion intended third-party capital mobilisation over time"
  true

williamsPowerInnovationJV : TransactionReceipt
williamsPowerInnovationJV = transaction-receipt
  "Williams Power Innovation JV"
  "Williams/Blackstone announcement, 13 July 2026"
  powerProjectEquity
  "Blackstone-led funds, in partnership with Apollo and KKR-managed insurance vehicles/accounts, committed capital for five Williams behind-the-meter Power Innovation projects spanning natural-gas supply/delivery and power for large loads including data-centre demand. The investors receive a 49% non-controlling equity interest."
  "USD 5.34 billion committed capital; 49% non-controlling interest"
  true

blackRockMirvacExposure : TransactionReceipt
blackRockMirvacExposure = transaction-receipt
  "BlackRock aggregate Mirvac exposure"
  "Mirvac FY25/FY26 substantial-holder disclosures"
  listedEquityExposure
  "BlackRock Group's disclosed Mirvac position increased from 263,029,096 stapled securities (6.66%) in 2025 to 303,997,515 (7.70%) in 2026. Mirvac has retail and residential/BTR assets; aggregate holding does not identify asset-specific economic exposure or operational control."
  "6.66% -> 7.70% disclosed Mirvac equity"
  true

------------------------------------------------------------------------
-- Same-actor cross-domain overlap.
------------------------------------------------------------------------

record CrossDomainReceipt : Set where
  constructor cross-domain-receipt
  field
    actor : String
    housingPaid : Bool
    aiComputePaid : Bool
    powerEnergyPaid : Bool
    sameLegalFundAcrossDomainsPaid : Bool
    reading : String
open CrossDomainReceipt public

apolloCrossDomain : CrossDomainReceipt
apolloCrossDomain = cross-domain-receipt
  "Apollo"
  true true true false
  "Apollo-managed capital is paid in institutional housing, AI compute and power infrastructure. The current receipts do not yet establish that the same exact fund/vehicle supplies capital in all three domains."

blackstoneCrossDomain : CrossDomainReceipt
blackstoneCrossDomain = cross-domain-receipt
  "Blackstone"
  true true true false
  "Blackstone-managed capital is paid in Australian home-loan finance, AI compute and power projects. Same-manager recurrence is not same-fund recurrence."

blackRockCrossDomain : CrossDomainReceipt
blackRockCrossDomain = cross-domain-receipt
  "BlackRock"
  true true false false
  "BlackRock has paid housing/property finance/portfolio exposure and is named in NVIDIA's AI-compute financing-platform initiative. This does not prove asset-specific operational control or a unified cross-domain mandate."

kkrCrossDomain : CrossDomainReceipt
kkrCrossDomain = cross-domain-receipt
  "KKR"
  false true true false
  "This receipt round pays KKR in NVIDIA AI-compute financing and Williams power-project capital. A comparable housing receipt is left to the dedicated housing sweep rather than inferred."

------------------------------------------------------------------------
-- Economic meaning of the receipts.
------------------------------------------------------------------------

record AssetClassConversion : Set where
  constructor asset-class-conversion
  field
    housingServiceCanBecomeRentOrMortgageCashflow : Bool
    computeServiceCanBecomeUsageLinkedCashflow : Bool
    powerServiceCanBecomeContractedInfrastructureCashflow : Bool
    recurringCashflowCanBeFinancedByInstitutionalCapital : Bool
    financingScaleProvesSocialAffordability : Bool
    financingScaleProvesIndependentTerminalDemand : Bool
    coFinancingProvesPoliticalCoordination : Bool
open AssetClassConversion public

canonicalAssetClassConversion : AssetClassConversion
canonicalAssetClassConversion = asset-class-conversion
  true true true true false false false

data SameManagerImpliesSameFund : Set where
data CoFinancingImpliesPoliticalCoordination : Set where
data MortgagePortfolioImpliesUnderlyingHouseTitle : Set where
data PlatformTargetImpliesRealisedDeployment : Set where
data CapitalCommitmentImpliesIndependentTerminalDemand : Set where

sameManagerDoesNotCreateSameFund : SameManagerImpliesSameFund → ⊥
sameManagerDoesNotCreateSameFund ()

coFinancingDoesNotCreatePoliticalCoordination : CoFinancingImpliesPoliticalCoordination → ⊥
coFinancingDoesNotCreatePoliticalCoordination ()

mortgagePortfolioDoesNotCreateUnderlyingHouseTitle : MortgagePortfolioImpliesUnderlyingHouseTitle → ⊥
mortgagePortfolioDoesNotCreateUnderlyingHouseTitle ()

platformTargetDoesNotCreateRealisedDeployment : PlatformTargetImpliesRealisedDeployment → ⊥
platformTargetDoesNotCreateRealisedDeployment ()

capitalCommitmentDoesNotCloseIndependentDemand : CapitalCommitmentImpliesIndependentTerminalDemand → ⊥
capitalCommitmentDoesNotCloseIndependentDemand ()

------------------------------------------------------------------------
-- Residual max-cut after paying manager-level recurrence.
------------------------------------------------------------------------

data ReceiptDebt : Set where
  sameFundCrossDomainLookthrough : ReceiptDebt
  housingInstrumentInventory : ReceiptDebt
  aiLeaseGuaranteeOfftakeInventory : ReceiptDebt
  publicSupportIncidence : ReceiptDebt
  epsteinBlackApolloSameObjectTransactionMap : ReceiptDebt

record ReceiptCut : Set where
  constructor receipt-cut
  field
    debt : ReceiptDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open ReceiptCut public

canonicalReceiptCuts : List ReceiptCut
canonicalReceiptCuts =
  receipt-cut epsteinBlackApolloSameObjectTransactionMap 100 true
    "Resolve historical Epstein-Leon Black/Apollo objects transaction-by-transaction: accounts, payments, fund interests, introductions, advisory work and counterparties; do not attribute Apollo-wide current strategy from Leon Black's personal relationship."
  ∷ receipt-cut sameFundCrossDomainLookthrough 100 true
    "Determine whether the recurring Apollo/Blackstone/BlackRock/KKR manager names conceal or reveal the same exact funds, insurers, mandates, lenders or syndicates across housing, AI and power."
  ∷ receipt-cut aiLeaseGuaranteeOfftakeInventory 99 true
    "Resolve AI-project leases, take-or-pay/offtake contracts, guarantees, customer concentration, vendor finance and residual-value risk behind the announced capital platforms."
  ∷ receipt-cut housingInstrumentInventory 99 true
    "Inventory housing exposure by legal instrument and geography: direct rental ownership, BTR development, mortgages/RMBS, listed REIT/property shares and private credit."
  ∷ receipt-cut publicSupportIncidence 98 true
    "Join tax concessions, public infrastructure, regulated revenue, guarantees and planning support to the privately captured housing/compute/power cashflows."
  ∷ []
