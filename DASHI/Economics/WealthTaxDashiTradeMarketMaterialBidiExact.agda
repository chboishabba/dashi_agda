module DASHI.Economics.WealthTaxDashiTradeMarketMaterialBidiExact where

-- CROSS-REPOSITORY SHADOW / SOURCE-OWNED FINANCE MAX-CUT, 2026-10-28.
-- dashiTRADE standalone runtime: chboishabba/dashiTRADE (separate owner).
-- Research direction: Johl Brown; source-written adapter: ChatGPT.
-- Original Norwegian portfolio and OECD empirical sources retain authorship.
-- This module is a finite counterexample, NOT a policy effect, live execution
-- receipt, firm-control measurement, physical-capacity observation or theorem
-- about an actual securities market. Existing Agda theorem owners are reused.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat using (_≤_; _∸_)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans; +-assoc; +-comm; m+n∸n≡m; [m+n]∸[m+o]≡n∸o)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong; cong₂)
open import Data.Empty using (⊥)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Economics.WealthTaxFiscalTransmissionControlBidi20261027Exact as Tax
import DASHI.Finance.DashiTradeFibreBridgeExact as Trade
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact as Finance

-- Do not collapse an assessed policy tax base, a situated trading fabric
-- and real financing conditions into one quoted equity price or tax number.
record PolicyTradeFinanceWorld : Set where
  constructor policy-trade-finance-world
  field
    fiscalExecution : Tax.FiscalExecution
    tradeExecutionContext : Trade.TradeSituatedFibre
    financingContext : Finance.InfrastructureMarketFabric
open PolicyTradeFinanceWorld public

taxAssessed : PolicyTradeFinanceWorld → Nat
taxAssessed state = Tax.assessedLiability (fiscalExecution state)

taxCollected : PolicyTradeFinanceWorld → Nat
taxCollected state = Tax.taxPaidCash (fiscalExecution state)

candidateDirection : PolicyTradeFinanceWorld → Dream.Direction
candidateDirection state =
  Dream.candidateObserver (Trade.tradeFabric (tradeExecutionContext state))

canBuy : PolicyTradeFinanceWorld → Bool
canBuy state =
  Dream.actionAvailable (Trade.tradeFabric (tradeExecutionContext state))
    Dream.buyAction

capitalDemandSignal :
  PolicyTradeFinanceWorld → Finance.InfrastructureMarketSignal
capitalDemandSignal state = Finance.signal (financingContext state)

refinanceViability :
  PolicyTradeFinanceWorld → Finance.RefinanceViability
refinanceViability state =
  Finance.refinanceViability (financingContext state)

-- All numbers/fibres below are inherited illustrative synthetic fixtures.
-- Same assessed tax and same headline demand signal, different buy/refinance
-- feasibility: neither liability nor the slogan "same demand" determines
-- actual market execution or physical infrastructure capacity.
cleanUnpaid : PolicyTradeFinanceWorld
cleanUnpaid = policy-trade-finance-world
  Tax.worldDueUnpaid Trade.cleanLongTradeFibre Finance.cleanDemandState

crowdedUnpaid : PolicyTradeFinanceWorld
crowdedUnpaid = policy-trade-finance-world
  Tax.worldDueUnpaid Trade.crowdedLongTradeFibre Finance.crowdedDemandState

cleanPaid : PolicyTradeFinanceWorld
cleanPaid = policy-trade-finance-world
  Tax.worldDuePaid Trade.cleanLongTradeFibre Finance.cleanDemandState

sameAssessedTax :
  taxAssessed cleanUnpaid ≡ taxAssessed crowdedUnpaid
sameAssessedTax = refl

sameDemand :
  capitalDemandSignal cleanUnpaid ≡ capitalDemandSignal crowdedUnpaid
sameDemand = Finance.sameDemandSignal

differentBuy :
  canBuy cleanUnpaid ≡ canBuy crowdedUnpaid → ⊥
differentBuy = Trade.buyAvailabilityDiffersAcrossTradeFibres

differentRefinancing :
  refinanceViability cleanUnpaid ≡
  refinanceViability crowdedUnpaid → ⊥
differentRefinancing = Finance.sameDemandDifferentRefinanceViability

-- The generic mathematical theorem is owned by INF, not original economists.
taxCannotFixBuyWitness : INF.NonFactorabilityWitness taxAssessed canBuy
taxCannotFixBuyWitness =
  INF.nonFactorabilityWitness
    cleanUnpaid crowdedUnpaid sameAssessedTax differentBuy

taxAmountCannotFixBuy :
  INF.FactorsThrough taxAssessed canBuy → ⊥
taxAmountCannotFixBuy =
  INF.witnessRulesOutEveryFlatFactorisation taxCannotFixBuyWitness

headlineDemandCannotFixRefinance :
  INF.FactorsThrough capitalDemandSignal refinanceViability → ⊥
headlineDemandCannotFixRefinance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      cleanUnpaid crowdedUnpaid sameDemand differentRefinancing)

-- BIDI: same suggested market action need not identify tax collection.
sameMarketProposal :
  candidateDirection cleanUnpaid ≡ candidateDirection cleanPaid
sameMarketProposal = refl

differentCash :
  taxCollected cleanUnpaid ≡ taxCollected cleanPaid → ⊥
differentCash ()

marketDirectionCannotFixCollection :
  INF.FactorsThrough candidateDirection taxCollected → ⊥
marketDirectionCannotFixCollection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      cleanUnpaid cleanPaid sameMarketProposal differentCash)

-- A tax policy has no direct permission to route an order in this module.
-- HOLD remains first class; no live broker, price forecast, or mandate.
holdStillAvailable :
  (world : PolicyTradeFinanceWorld) →
  Dream.Available
    (Trade.tradeFabric (tradeExecutionContext world)) Dream.holdAction
holdStillAvailable world =
  Dream.holdAlwaysAvailable (Trade.tradeFabric (tradeExecutionContext world))

data AssessedLiabilityCreatesMarketOrder : Set where
data TradingProfitEstablishesTaxPolicyCausation : Set where
data MarketPriceCreatesPhysicalInfrastructure : Set where

taxLiabilityIsNotTradingPermission :
  AssessedLiabilityCreatesMarketOrder → ⊥
taxLiabilityIsNotTradingPermission ()

profitIsNotTaxPolicyCausation :
  TradingProfitEstablishesTaxPolicyCausation → ⊥
profitIsNotTaxPolicyCausation ()

priceDoesNotBuildPhysicalCapacity :
  MarketPriceCreatesPhysicalInfrastructure → ⊥
priceDoesNotBuildPhysicalCapacity ()


------------------------------------------------------------------------
-- FINANCING TRANSMISSION MAX-CUT: PAYING A TAX IS NOT SELLING STOCK.
--
-- The owner and date belong to this DASHI application only. This exact
-- source-written fixture is not a tax-statute statement or a trade receipt.
-- Borrowing, cash payment and asset-sale proceeds are separate financing
-- channels. Identical received revenue may have distinct route/cost effects.
------------------------------------------------------------------------

record FundingRoute : Set where
  constructor funding-route
  field
    taxExecution : Tax.FiscalExecution
    unrestrictedCash : Nat
    newLoanCash : Nat
    grossSaleCash : Nat
    shareUnitsSold : Nat
    executionCashCost : Nat
    installedMachineUnits : Nat
    -- A *model fixture accounting identity*, not an observed economy law.
    fundingBalances :
      unrestrictedCash + newLoanCash + grossSaleCash
      ≡ Tax.taxPaidCash taxExecution + executionCashCost
open FundingRoute public

-- Conditional POSITIVE result: only within this exactly balanced fixture.
-- If both opening unrestricted cash and new loan proceeds are unavailable,
-- gross sale receipts must cover the realised tax payment plus execution
-- cash costs. No statement about real-world forced sales is inferred.
noOtherFundingImpliesSaleProceeds :
  (route : FundingRoute) →
  unrestrictedCash route ≡ 0 →
  newLoanCash route ≡ 0 →
  grossSaleCash route ≡
    Tax.taxPaidCash (taxExecution route) + executionCashCost route
noOtherFundingImpliesSaleProceeds route noCash noLoan
  rewrite noCash | noLoan = fundingBalances route

taxPaymentForRoute : FundingRoute → Nat
taxPaymentForRoute route = Tax.taxPaidCash (taxExecution route)

cashFunded : FundingRoute
cashFunded =
  funding-route Tax.worldDuePaid 2 0 0 0 0 9 refl

assetSaleFunded : FundingRoute
assetSaleFunded =
  funding-route Tax.worldDuePaid 0 0 3 2 1 9 refl

debtFunded : FundingRoute
debtFunded =
  funding-route Tax.worldDuePaid 0 2 0 0 0 9 refl

higherCostSameSaleUnits : FundingRoute
higherCostSameSaleUnits =
  funding-route Tax.worldDuePaid 0 0 4 2 2 9 refl

sameSaleButLessInstalledCapacity : FundingRoute
sameSaleButLessInstalledCapacity =
  funding-route Tax.worldDuePaid 0 0 3 2 1 0 refl

equalTaxPaymentDifferentSaleVolume :
  taxPaymentForRoute cashFunded ≡
  taxPaymentForRoute assetSaleFunded
equalTaxPaymentDifferentSaleVolume = refl

saleVolumeDiffersAtEqualPayment :
  shareUnitsSold cashFunded ≡ shareUnitsSold assetSaleFunded → ⊥
saleVolumeDiffersAtEqualPayment ()

paidTaxCannotDetermineUnitsSold :
  INF.FactorsThrough taxPaymentForRoute shareUnitsSold → ⊥
paidTaxCannotDetermineUnitsSold =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      cashFunded assetSaleFunded
      equalTaxPaymentDifferentSaleVolume
      saleVolumeDiffersAtEqualPayment)

sameSoldSharesDifferentExecutionCost :
  shareUnitsSold assetSaleFunded ≡
  shareUnitsSold higherCostSameSaleUnits
sameSoldSharesDifferentExecutionCost = refl

executionCostDiffers :
  executionCashCost assetSaleFunded ≡
  executionCashCost higherCostSameSaleUnits → ⊥
executionCostDiffers ()

saleVolumeCannotDetermineExecutionCost :
  INF.FactorsThrough shareUnitsSold executionCashCost → ⊥
saleVolumeCannotDetermineExecutionCost =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      assetSaleFunded higherCostSameSaleUnits
      sameSoldSharesDifferentExecutionCost executionCostDiffers)

sameSaleVolumeWithDifferentInstalledMachines :
  shareUnitsSold assetSaleFunded ≡
  shareUnitsSold sameSaleButLessInstalledCapacity
sameSaleVolumeWithDifferentInstalledMachines = refl

installedMachineCountDiffers :
  installedMachineUnits assetSaleFunded ≡
  installedMachineUnits sameSaleButLessInstalledCapacity → ⊥
installedMachineCountDiffers ()

saleVolumeCannotDeterminePhysicalCapacity :
  INF.FactorsThrough shareUnitsSold installedMachineUnits → ⊥
saleVolumeCannotDeterminePhysicalCapacity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      assetSaleFunded sameSaleButLessInstalledCapacity
      sameSaleVolumeWithDifferentInstalledMachines
      installedMachineCountDiffers)

data TaxPaymentRequiresForcedLiquidation : Set where
data EqualSharesSoldMeanEqualMarketImpact : Set where

taxPaymentDoesNotForceLiquidation :
  TaxPaymentRequiresForcedLiquidation → ⊥
taxPaymentDoesNotForceLiquidation ()

equalVolumeDoesNotProveEqualMarketImpact :
  EqualSharesSoldMeanEqualMarketImpact → ⊥
equalVolumeDoesNotProveEqualMarketImpact ()

-- Distinct scoped upstream original empirical roots:
-- Fagereng/Guiso/Ring 2026 NBER 35262: investor response in Norway.
-- Minsoo Kim, Management Science, 2026, DOI 10.1287/mnsc.2025.01690:
--   forced bond-fund redemptions x market liquidity in corporate bonds,
--   NOT wealth-tax sales.
-- Bianchi/Ceneri/Melosi/Villa, NBER 35715, September 2026:
--   heterogeneous-agents funded/unfunded transfer model, NOT proof of a
--   realised tax-cap market-price, physical-resource or refinancing effect.


------------------------------------------------------------------------
-- SAME-OBJECT OWNERSHIP HANDOFF: A SALE VOLUME DOES NOT IDENTIFY ITS CLASS.
-- Actual independent company registers, transfer contracts and vote classes
-- are required before invoking this *optional* reconciliation interface.
-- The financing-route count alone has NO company-control authority.
------------------------------------------------------------------------

record FundingVoteReconciliation : Set where
  constructor funding-vote-reconciliation
  field
    routedPayment : FundingRoute
    shareStateBefore : Tax.ShareVoteState
    shareStateAfter : Tax.ShareVoteState
    ordinaryUnitsTransferred : Nat
    superVotingUnitsTransferred : Nat
    matchedSaleCount :
      ordinaryUnitsTransferred + superVotingUnitsTransferred
      ≡ shareUnitsSold routedPayment
    ownerOrdinaryReconciled :
      Tax.ownerOrdinaryShares shareStateBefore
      ≡ Tax.ownerOrdinaryShares shareStateAfter + ordinaryUnitsTransferred
    ownerSuperReconciled :
      Tax.ownerSuperVotingShares shareStateBefore
      ≡ Tax.ownerSuperVotingShares shareStateAfter
        + superVotingUnitsTransferred
    ordinaryTotalUnchanged :
      Tax.allOrdinaryShares shareStateBefore
      ≡ Tax.allOrdinaryShares shareStateAfter
    superTotalUnchanged :
      Tax.allSuperVotingShares shareStateBefore
      ≡ Tax.allSuperVotingShares shareStateAfter
open FundingVoteReconciliation public

ordinarySaleLink : FundingVoteReconciliation
ordinarySaleLink =
  funding-vote-reconciliation
    assetSaleFunded
    (Tax.share-vote-state 6 3 20 3)
    (Tax.share-vote-state 4 3 20 3)
    2 0 refl refl refl refl refl

superVotingSaleLink : FundingVoteReconciliation
superVotingSaleLink =
  funding-vote-reconciliation
    assetSaleFunded
    (Tax.share-vote-state 6 3 20 3)
    (Tax.share-vote-state 6 1 20 3)
    0 2 refl refl refl refl refl

routedUnitsSold : FundingVoteReconciliation → Nat
routedUnitsSold link = shareUnitsSold (routedPayment link)

weightedOwnerVotesAfter : FundingVoteReconciliation → Nat
weightedOwnerVotesAfter link =
  Tax.ownerWeightedVotes (shareStateAfter link)

equalSaleCountAcrossClasses :
  routedUnitsSold ordinarySaleLink ≡ routedUnitsSold superVotingSaleLink
equalSaleCountAcrossClasses = refl

ordinaryRouteLeaves34Votes :
  weightedOwnerVotesAfter ordinarySaleLink ≡ 34
ordinaryRouteLeaves34Votes = refl

superRouteLeaves16Votes :
  weightedOwnerVotesAfter superVotingSaleLink ≡ 16
superRouteLeaves16Votes = refl

differentVotesAfterSameCount :
  weightedOwnerVotesAfter ordinarySaleLink
  ≡ weightedOwnerVotesAfter superVotingSaleLink → ⊥
differentVotesAfterSameCount ()

quantityCannotFixVotingControl :
  INF.FactorsThrough routedUnitsSold weightedOwnerVotesAfter → ⊥
quantityCannotFixVotingControl =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      ordinarySaleLink superVotingSaleLink
      equalSaleCountAcrossClasses differentVotesAfterSameCount)

-- 34/50 and 16/50 are fixture voting weights. This is not a legal
-- board-control determination, a registered ownership record, nor a model
-- of beneficial owner chains, voting pacts or fiduciary agreements.


------------------------------------------------------------------------
-- SETTLED TRANSACTION SUBCUT: ORDER != EXECUTION != CASH SETTLEMENT.
-- A settlement cash entry is not present merely because a trade was proposed
-- or executed. We impose same-route quantity and cash equalities explicitly.
-- This remains a synthetic finite proof, NOT a custodian or broker receipt.
-- Prior original proof: DASHI.Core.IntersectionalNonFactorability.
------------------------------------------------------------------------

record TwoFillSettlementLink : Set where
  constructor two-fill-settlement-link
  field
    settledFundingRoute : FundingRoute
    submittedUnits : Nat
    firstExecutedUnits : Nat
    secondExecutedUnits : Nat
    firstSettledUnits : Nat
    secondSettledUnits : Nat
    firstUnitPrice : Nat
    secondUnitPrice : Nat
    unfilledUnits : Nat
    firstUnsettledUnits : Nat
    secondUnsettledUnits : Nat
    proposedUnitsReconciled :
      submittedUnits ≡
        firstExecutedUnits + secondExecutedUnits + unfilledUnits
    firstFillReconciled :
      firstExecutedUnits ≡ firstSettledUnits + firstUnsettledUnits
    secondFillReconciled :
      secondExecutedUnits ≡ secondSettledUnits + secondUnsettledUnits
    settledVolumeReconciled :
      shareUnitsSold settledFundingRoute ≡
        firstSettledUnits + secondSettledUnits
    settledProceedsReconciled :
      grossSaleCash settledFundingRoute ≡
        firstSettledUnits * firstUnitPrice
        + secondSettledUnits * secondUnitPrice
open TwoFillSettlementLink public

-- Same two-unit order submitted but not filled: paid from opening cash.
submittedWithoutFill : TwoFillSettlementLink
submittedWithoutFill =
  two-fill-settlement-link
    cashFunded
    2 0 0 0 0 0 0 2 0 0
    refl refl refl refl refl

-- Two separate unit fills at distinct gross prices 1 and 2 produce 3.
-- Exactly 2 settled units, 3 proceeds, 1 paid execution cash cost and
-- 2 tax cash collected under the earlier assetSaleFunded balance.
twoPricesThreeProceeds : TwoFillSettlementLink
twoPricesThreeProceeds =
  two-fill-settlement-link
    assetSaleFunded
    2 1 1 1 1 1 2 0 0 0
    refl refl refl refl refl

-- The full order executed, but no unit has actually settled.
executedUnsettled : TwoFillSettlementLink
executedUnsettled =
  two-fill-settlement-link
    cashFunded
    2 2 0 0 0 3 0 0 2 0
    refl refl refl refl refl

settledShareCount : TwoFillSettlementLink → Nat
settledShareCount link =
  firstSettledUnits link + secondSettledUnits link

executedShareCount : TwoFillSettlementLink → Nat
executedShareCount link =
  firstExecutedUnits link + secondExecutedUnits link

sameSubmittedUnits :
  submittedUnits submittedWithoutFill ≡ submittedUnits twoPricesThreeProceeds
sameSubmittedUnits = refl

differentSettlementAtSameSubmittedUnits :
  settledShareCount submittedWithoutFill ≡
  settledShareCount twoPricesThreeProceeds → ⊥
differentSettlementAtSameSubmittedUnits ()

submittedOrderDoesNotDetermineSettlement :
  INF.FactorsThrough submittedUnits settledShareCount → ⊥
submittedOrderDoesNotDetermineSettlement =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      submittedWithoutFill twoPricesThreeProceeds
      sameSubmittedUnits differentSettlementAtSameSubmittedUnits)

sameExecutedUnits :
  executedShareCount executedUnsettled ≡
  executedShareCount twoPricesThreeProceeds
sameExecutedUnits = refl

differentSettlementAtSameExecutedUnits :
  settledShareCount executedUnsettled ≡
  settledShareCount twoPricesThreeProceeds → ⊥
differentSettlementAtSameExecutedUnits ()

executionDoesNotDetermineSettlement :
  INF.FactorsThrough executedShareCount settledShareCount → ⊥
executionDoesNotDetermineSettlement =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      executedUnsettled twoPricesThreeProceeds
      sameExecutedUnits differentSettlementAtSameExecutedUnits)

-- A matching synthetic receipt states only the stipulated equality.
-- It is not an actual cleared exchange or custodian bank statement.
twoFillCashConservation :
  grossSaleCash (settledFundingRoute twoPricesThreeProceeds) ≡
    firstSettledUnits twoPricesThreeProceeds
      * firstUnitPrice twoPricesThreeProceeds
    + secondSettledUnits twoPricesThreeProceeds
      * secondUnitPrice twoPricesThreeProceeds
twoFillCashConservation =
  settledProceedsReconciled twoPricesThreeProceeds


------------------------------------------------------------------------
-- CONDITIONAL CASH CHRONOLOGY
-- An order/execution event is not exchange settlement. For a sale-funded
-- TAX PAYMENT to use settled proceeds, source times must be matched.
-- A bridge loan (if one exists) is a separate FundingRoute.newLoanCash axis;
-- do not invent it merely because settlement is later than tax payment.
------------------------------------------------------------------------

record MatchedSettlementTaxChronology : Set where
  constructor matched-settlement-tax-chronology
  field
    settledTransaction : TwoFillSettlementLink
    finalSettlementEpoch : Nat
    taxCashReceiptEpoch : Nat
    forwardSettlementToCollectionLag : Nat
    taxCashNotEarlierThanSettlement :
      taxCashReceiptEpoch ≡
        finalSettlementEpoch + forwardSettlementToCollectionLag
open MatchedSettlementTaxChronology public

-- Chronological integer epochs are synthetic ordered markers, not dated
-- market observations and not automatically exchange-business-day offsets.
sameRouteChronologicalPayment : MatchedSettlementTaxChronology
sameRouteChronologicalPayment =
  matched-settlement-tax-chronology
    twoPricesThreeProceeds 3 4 1 refl

-- A hypothetical settled sale at epoch 3 cannot directly fund a tax cash
-- receipt at epoch 1 under this specific nonnegative forward-lag contract.
priorCashReceiptHasNoForwardSettlementLink :
  (lag : Nat) → 1 ≡ 3 + lag → ⊥
priorCashReceiptHasNoForwardSettlementLink zero ()
priorCashReceiptHasNoForwardSettlementLink (suc lag) ()


------------------------------------------------------------------------
-- INSTRUMENT-CLASS SAME-OBJECT SUBCUT
-- Aggregate sale units are not an issuer/instrument/class identification.
-- The source-key labels below are synthetic fields, not custody records.
-- Ownership and intellectual priority for the generic result remain in INF.
------------------------------------------------------------------------

data SettlementInstrumentClass : Set where
  ordinarySecurity : SettlementInstrumentClass
  superVotingSecurity : SettlementInstrumentClass

ClassCompatibleWithTransfer :
  SettlementInstrumentClass → FundingVoteReconciliation → Set
ClassCompatibleWithTransfer ordinarySecurity link =
  superVotingUnitsTransferred link ≡ 0
ClassCompatibleWithTransfer superVotingSecurity link =
  ordinaryUnitsTransferred link ≡ 0

record IdentifiedClassSettlement : Set where
  constructor identified-class-settlement
  field
    matchedClassTransfer : FundingVoteReconciliation
    issuerReference : String
    instrumentReference : String
    instrumentClass : SettlementInstrumentClass
    transferMatchesNamedClass :
      ClassCompatibleWithTransfer instrumentClass matchedClassTransfer
open IdentifiedClassSettlement public

syntheticOrdinarySettlement : IdentifiedClassSettlement
syntheticOrdinarySettlement =
  identified-class-settlement
    ordinarySaleLink "fixture-issuer" "fixture-ordinary"
    ordinarySecurity refl

syntheticSuperSettlement : IdentifiedClassSettlement
syntheticSuperSettlement =
  identified-class-settlement
    superVotingSaleLink "fixture-issuer" "fixture-super"
    superVotingSecurity refl

saleUnitsOfInstrument : IdentifiedClassSettlement → Nat
saleUnitsOfInstrument state =
  routedUnitsSold (matchedClassTransfer state)

sameTwoUnitsDifferentClasses :
  saleUnitsOfInstrument syntheticOrdinarySettlement ≡
  saleUnitsOfInstrument syntheticSuperSettlement
sameTwoUnitsDifferentClasses = refl

distinctClassesDespiteSameVolume :
  instrumentClass syntheticOrdinarySettlement ≡
  instrumentClass syntheticSuperSettlement → ⊥
distinctClassesDespiteSameVolume ()

saleVolumeCannotIdentifyInstrumentClass :
  INF.FactorsThrough saleUnitsOfInstrument instrumentClass → ⊥
saleVolumeCannotIdentifyInstrumentClass =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      syntheticOrdinarySettlement syntheticSuperSettlement
      sameTwoUnitsDifferentClasses distinctClassesDespiteSameVolume)

-- The strings are source labels only: matching them without transfer and
-- legal registers proves neither shared economic ownership nor legal power.


------------------------------------------------------------------------
-- SAME-OBJECT CASH/RIGHTS WELD AND CLEARING-NET OBSERVER
-- Direct reuse of source-owned INF nonfactorability and earlier fixture types.
-- The witness requires exact agreement on finance route, units, issuer and
-- instrument labels, but NO label proves a real custodial/issuer register.
-- The external legal, broker and tax source inputs are NOT fabricated here.
------------------------------------------------------------------------

record SettlementOwnershipWeld : Set where
  constructor settlement-ownership-weld
  field
    settledTrade : TwoFillSettlementLink
    identifiedOwnerTransfer : IdentifiedClassSettlement
    settledIssuerLabel : String
    settledInstrumentLabel : String
    routeMatches :
      settledFundingRoute settledTrade ≡
        routedPayment (matchedClassTransfer identifiedOwnerTransfer)
    settledUnitsMatch :
      settledShareCount settledTrade ≡
        saleUnitsOfInstrument identifiedOwnerTransfer
    issuerLabelMatches :
      settledIssuerLabel ≡ issuerReference identifiedOwnerTransfer
    instrumentLabelMatches :
      settledInstrumentLabel ≡ instrumentReference identifiedOwnerTransfer
open SettlementOwnershipWeld public

syntheticOrdinaryWeld : SettlementOwnershipWeld
syntheticOrdinaryWeld =
  settlement-ownership-weld
    twoPricesThreeProceeds syntheticOrdinarySettlement
    "fixture-issuer" "fixture-ordinary"
    refl refl refl refl

syntheticSuperVotingWeld : SettlementOwnershipWeld
syntheticSuperVotingWeld =
  settlement-ownership-weld
    twoPricesThreeProceeds syntheticSuperSettlement
    "fixture-issuer" "fixture-super"
    refl refl refl refl

-- ASX/CHESS source root: participant-level netting takes place before
-- DvP settlement. In particular, net cash receipt does not reconstruct
-- a participant's GROSS buy/sell orders or any person's tax-sale proceeds.
-- Source: ASX "Settlement services and pricing", 2026-accessed official page.
-- This finite non-negative NET-RECEIPT fixture omits participants who pay net.
record ParticipantClearingBatch : Set where
  constructor participant-clearing-batch
  field
    grossSellCash : Nat
    grossBuyCash : Nat
    netReceivedCash : Nat
    netAccounting :
      grossSellCash ≡ grossBuyCash + netReceivedCash
open ParticipantClearingBatch public

noClearedTransactions : ParticipantClearingBatch
noClearedTransactions =
  participant-clearing-batch 0 0 0 refl

offsettingClearedTransactions : ParticipantClearingBatch
offsettingClearedTransactions =
  participant-clearing-batch 3 3 0 refl

sameNetReceipt :
  netReceivedCash noClearedTransactions ≡
  netReceivedCash offsettingClearedTransactions
sameNetReceipt = refl

differentGrossSellsDespiteSameNet :
  grossSellCash noClearedTransactions ≡
  grossSellCash offsettingClearedTransactions → ⊥
differentGrossSellsDespiteSameNet ()

netReceiptCannotRecoverGrossTurnover :
  INF.FactorsThrough netReceivedCash grossSellCash → ⊥
netReceiptCannotRecoverGrossTurnover =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      noClearedTransactions offsettingClearedTransactions
      sameNetReceipt differentGrossSellsDespiteSameNet)

-- Signed cash obligation direction is a tagged variant, not negative Nat.
-- This extends the receiver-only finite ParticipantClearingBatch owner without
-- conflating a paying participant with a receiving participant.

data ParticipantCashDirection : Set where
  netCashReceivable : ParticipantCashDirection
  netCashPayable : ParticipantCashDirection

DirectionBalanced :
  ParticipantCashDirection → Nat → Nat → Nat → Set
DirectionBalanced netCashReceivable grossSell grossBuy net =
  grossSell ≡ grossBuy + net
DirectionBalanced netCashPayable grossSell grossBuy net =
  grossBuy ≡ grossSell + net

record DirectionalClearingBatch : Set where
  constructor directional-clearing-batch
  field
    cashDirection : ParticipantCashDirection
    grossSellSettlementCash : Nat
    grossBuySettlementCash : Nat
    netSettlementCashMagnitude : Nat
    directionBalance :
      DirectionBalanced cashDirection
        grossSellSettlementCash grossBuySettlementCash
        netSettlementCashMagnitude
open DirectionalClearingBatch public

directionalParticipantCashBalance :
  (batch : DirectionalClearingBatch) →
  DirectionBalanced (cashDirection batch)
    (grossSellSettlementCash batch)
    (grossBuySettlementCash batch)
    (netSettlementCashMagnitude batch)
directionalParticipantCashBalance =
  directionBalance

receivingParticipantExample : DirectionalClearingBatch
receivingParticipantExample =
  directional-clearing-batch netCashReceivable 5 2 3 refl

payingParticipantExample : DirectionalClearingBatch
payingParticipantExample =
  directional-clearing-batch netCashPayable 2 5 3 refl

-- Cash magnitudes and this directional cash balance do NOT certify the
-- securities-leg net quantities, eligibility or the DvP settlement receipt.

------------------------------------------------------------------------
-- CONDITIONAL SINGLE-INSTRUMENT DELIVERY VERSUS PAYMENT (F04/F05).
-- The independent settlement authority / source finality remains absent
-- until supplied externally. No T+1/T+2 calendar or market clock inferred.
------------------------------------------------------------------------

data SecurityNetDirection : Set where
  netSecuritiesDelivered : SecurityNetDirection
  netSecuritiesReceived : SecurityNetDirection

SecurityQuantityBalanced :
  SecurityNetDirection → Nat → Nat → Nat → Set
SecurityQuantityBalanced netSecuritiesDelivered grossDelivered grossReceived net =
  grossDelivered ≡ grossReceived + net
SecurityQuantityBalanced netSecuritiesReceived grossDelivered grossReceived net =
  grossReceived ≡ grossDelivered + net

data OppositeCashAndSecurityLeg :
  ParticipantCashDirection → SecurityNetDirection → Set where
  sellSettlementLegs :
    OppositeCashAndSecurityLeg netCashReceivable netSecuritiesDelivered
  purchaseSettlementLegs :
    OppositeCashAndSecurityLeg netCashPayable netSecuritiesReceived

record SingleInstrumentDvPBatch : Set where
  constructor single-instrument-dvp-batch
  field
    linkedCashBatch : DirectionalClearingBatch
    securityIdentifier : String
    securityDirection : SecurityNetDirection
    grossDeliveredUnits : Nat
    grossReceivedUnits : Nat
    netSecurityUnits : Nat
    securityQuantityReconciled :
      SecurityQuantityBalanced securityDirection
        grossDeliveredUnits grossReceivedUnits netSecurityUnits
    cashToSecurityDirectionMatched :
      OppositeCashAndSecurityLeg
        (cashDirection linkedCashBatch) securityDirection
    cashFinalityEpoch : Nat
    titleFinalityEpoch : Nat
    simultaneousFinalityRecorded :
      cashFinalityEpoch ≡ titleFinalityEpoch
open SingleInstrumentDvPBatch public

aggregateNetPositionsRespectGrossCashAndSecurityTotals :
  (batch : SingleInstrumentDvPBatch) →
  DirectionBalanced
    (cashDirection (linkedCashBatch batch))
    (grossSellSettlementCash (linkedCashBatch batch))
    (grossBuySettlementCash (linkedCashBatch batch))
    (netSettlementCashMagnitude (linkedCashBatch batch))
  × SecurityQuantityBalanced
      (securityDirection batch)
      (grossDeliveredUnits batch)
      (grossReceivedUnits batch)
      (netSecurityUnits batch)
aggregateNetPositionsRespectGrossCashAndSecurityTotals batch =
  directionBalance (linkedCashBatch batch) ,
  securityQuantityReconciled batch

deliveryVersusPaymentCashAndTitleCoMove :
  (batch : SingleInstrumentDvPBatch) →
  cashFinalityEpoch batch ≡ titleFinalityEpoch batch
deliveryVersusPaymentCashAndTitleCoMove =
  simultaneousFinalityRecorded

syntheticDeliveredDvP : SingleInstrumentDvPBatch
syntheticDeliveredDvP =
  single-instrument-dvp-batch
    receivingParticipantExample
    "fixture:eligible-security-ordinary"
    netSecuritiesDelivered
    5 2 3 refl sellSettlementLegs
    4 4 refl

-- F04/F05 close only the model's proof obligations WHEN a caller supplies
-- a batch witness. Neither model field represents official ASX/CHESS data.

-- Reconcile arbitrarily many investor allocations to a participant-level
-- cash batch. The investors' identity, settlement authority and instrument
-- eligibility remain additional external inputs, not inferred from amounts.

sumInvestorCashUnits : List Nat → Nat
sumInvestorCashUnits [] = zero
sumInvestorCashUnits (units ∷ rest) =
  units + sumInvestorCashUnits rest

record ParticipantInvestorAllocation : Set where
  constructor participant-investor-allocation
  field
    netBatch : ParticipantClearingBatch
    investorGrossSales : List Nat
    investorGrossPurchases : List Nat
    sellerAllocationsReconciled :
      sumInvestorCashUnits investorGrossSales ≡ grossSellCash netBatch
    buyerAllocationsReconciled :
      sumInvestorCashUnits investorGrossPurchases ≡ grossBuyCash netBatch
open ParticipantInvestorAllocation public

investorAllocationsSumToParticipantObligation :
  (allocation : ParticipantInvestorAllocation) →
  sumInvestorCashUnits (investorGrossSales allocation) ≡
    sumInvestorCashUnits (investorGrossPurchases allocation)
      + netReceivedCash (netBatch allocation)
investorAllocationsSumToParticipantObligation allocation =
  trans
    (sellerAllocationsReconciled allocation)
    (trans
      (netAccounting (netBatch allocation))
      (cong (λ cash → cash + netReceivedCash (netBatch allocation))
        (sym (buyerAllocationsReconciled allocation))))

syntheticOffsettingInvestorAllocations : ParticipantInvestorAllocation
syntheticOffsettingInvestorAllocations =
  participant-investor-allocation
    offsettingClearedTransactions
    (1 ∷ 2 ∷ [])
    (3 ∷ [])
    refl refl

-- Allocation evidence is required, not recovered automatically from
-- participant cash, identical digest strings or an issuer reference alone.

-- The net batch is a participant-level financial observation. The
-- original two-fill sale is an investor-level synthetic fixture. No implicit
-- identification of the two records is supplied by this code.


------------------------------------------------------------------------
------------------------------------------------------------------------
-- BORROWING INCREASES DEBT ALONG WITH CASH (C07).
-- Net position here is cash minus liabilities truncated at zero. This is
-- an explicitly local financial stock model: no interest, collateral,
-- lender risk, fees, taxes, valuation change or repayment is inferred.
------------------------------------------------------------------------

record MatchedBorrowingBalance : Set where
  constructor matched-borrowing-balance
  field
    cashBeforeBorrowing : Nat
    debtBeforeBorrowing : Nat
    cashBorrowed : Nat
    cashAfterBorrowing : Nat
    debtAfterBorrowing : Nat
    cashIncreaseMatched :
      cashAfterBorrowing ≡ cashBorrowed + cashBeforeBorrowing
    debtIncreaseMatched :
      debtAfterBorrowing ≡ cashBorrowed + debtBeforeBorrowing
open MatchedBorrowingBalance public

loanProceedsIncreaseLiabilities :
  (loan : MatchedBorrowingBalance) →
  debtAfterBorrowing loan ≡
    cashBorrowed loan + debtBeforeBorrowing loan
loanProceedsIncreaseLiabilities = debtIncreaseMatched

borrowedCashDoesNotByItselfRaiseNetCashMinusDebt :
  (loan : MatchedBorrowingBalance) →
  cashAfterBorrowing loan ∸ debtAfterBorrowing loan ≡
    cashBeforeBorrowing loan ∸ debtBeforeBorrowing loan
borrowedCashDoesNotByItselfRaiseNetCashMinusDebt loan =
  trans
    (cong₂ _∸_ (cashIncreaseMatched loan) (debtIncreaseMatched loan))
    ([m+n]∸[m+o]≡n∸o (cashBorrowed loan)
      (cashBeforeBorrowing loan) (debtBeforeBorrowing loan))

syntheticBorrowedFunding : MatchedBorrowingBalance
syntheticBorrowedFunding =
  matched-borrowing-balance 2 1 3 5 4 refl refl

-- Cash, debt and true wealth are not the same thing. The positive
-- conservation statement depends on both ledger identities, not on merely
-- observing that a bank account balance increased.

-- GENERIC FINITE ORDER/EXECUTION/SETTLEMENT CONTRACTS (D09--D11).
-- No two-fill bound is silently assumed to cover an arbitrary collection.
-- A valid reconciled receipt carries accounting evidence. Mere proposal,
-- request, fill ID, or market signal does NOT construct such a receipt.
------------------------------------------------------------------------

record CountReconciledOrder : Set where
  constructor count-reconciled-order
  field
    submittedCount : Nat
    executedCount : Nat
    settledCount : Nat
    unfilledCount : Nat
    unsettledCount : Nat
    submittedCountReconciled :
      submittedCount ≡ executedCount + unfilledCount
    executedCountReconciled :
      executedCount ≡ settledCount + unsettledCount
open CountReconciledOrder public

genericExecutedCountBoundedBySubmitted :
  (receipt : CountReconciledOrder) →
  executedCount receipt ≤ submittedCount receipt
genericExecutedCountBoundedBySubmitted receipt =
  subst (λ n → executedCount receipt ≤ n)
        (sym (submittedCountReconciled receipt))
        (m≤m+n (executedCount receipt) (unfilledCount receipt))

genericSettledCountBoundedByExecuted :
  (receipt : CountReconciledOrder) →
  settledCount receipt ≤ executedCount receipt
genericSettledCountBoundedByExecuted receipt =
  subst (λ n → settledCount receipt ≤ n)
        (sym (executedCountReconciled receipt))
        (m≤m+n (settledCount receipt) (unsettledCount receipt))

record PriceQuantityFill : Set where
  constructor price-quantity-fill
  field
    clearedUnits : Nat
    quotedUnitPrice : Nat
open PriceQuantityFill public

grossFromFiniteSettledFills : List PriceQuantityFill → Nat
grossFromFiniteSettledFills [] = zero
grossFromFiniteSettledFills (fill ∷ rest) =
  clearedUnits fill * quotedUnitPrice fill
  + grossFromFiniteSettledFills rest

unitsFromFiniteSettledFills : List PriceQuantityFill → Nat
unitsFromFiniteSettledFills [] = zero
unitsFromFiniteSettledFills (fill ∷ rest) =
  clearedUnits fill + unitsFromFiniteSettledFills rest

record CashReconciledFillBatch : Set where
  constructor cash-reconciled-fill-batch
  field
    countReceipt : CountReconciledOrder
    settledFills : List PriceQuantityFill
    recordedGrossCash : Nat
    fillCountMatchesReceipt :
      unitsFromFiniteSettledFills settledFills ≡
        settledCount countReceipt
    settledProceedsMatchRecordedCash :
      recordedGrossCash ≡ grossFromFiniteSettledFills settledFills
open CashReconciledFillBatch public

genericSettledProceedsIsExactPriceQuantitySum :
  (batch : CashReconciledFillBatch) →
  recordedGrossCash batch ≡ grossFromFiniteSettledFills (settledFills batch)
genericSettledProceedsIsExactPriceQuantitySum =
  settledProceedsMatchRecordedCash

-- Arbitrarily many fills use the same generic conservation contract.
-- All prices here are dimensionless natural-number fixture units, not
-- market prices, fiat cents, broker fees or settlement confirmations.
twoFillGenericWitness : CashReconciledFillBatch
twoFillGenericWitness =
  cash-reconciled-fill-batch
    (count-reconciled-order 2 2 2 0 0 refl refl)
    (price-quantity-fill 1 1 ∷ price-quantity-fill 1 2 ∷ [])
    3 refl refl

genericSettledCountBoundedBySubmitted :
  (receipt : CountReconciledOrder) →
  settledCount receipt ≤ submittedCount receipt
genericSettledCountBoundedBySubmitted receipt =
  ≤-trans
    (genericSettledCountBoundedByExecuted receipt)
    (genericExecutedCountBoundedBySubmitted receipt)

twoFillGenericBound :
  settledCount (countReceipt twoFillGenericWitness)
    ≤ submittedCount (countReceipt twoFillGenericWitness)
twoFillGenericBound =
  genericSettledCountBoundedBySubmitted (countReceipt twoFillGenericWitness)

twoFillGenericCash :
  recordedGrossCash twoFillGenericWitness ≡ 3
twoFillGenericCash = refl


------------------------------------------------------------------------
-- EXACT SHARE TRANSFER CONSERVATION (E06).
-- This is a transfer of already issued units between two accounts, not
-- issuance/cancellation, derivatives, control rights or beneficial title.
-- No settlement-finality or source-authentication proof is constructed.
------------------------------------------------------------------------

record PureIssuedClassTransfer : Set where
  constructor pure-issued-class-transfer
  field
    sellerUnitsBefore : Nat
    sellerUnitsAfter : Nat
    buyerUnitsBefore : Nat
    buyerUnitsAfter : Nat
    transferredUnits : Nat
    sellerReconciled :
      sellerUnitsBefore ≡ sellerUnitsAfter + transferredUnits
    buyerReconciled :
      buyerUnitsAfter ≡ buyerUnitsBefore + transferredUnits
open PureIssuedClassTransfer public

shareClassTransferPreservesIssuedSupply :
  (t : PureIssuedClassTransfer) →
  sellerUnitsBefore t + buyerUnitsBefore t
    ≡ sellerUnitsAfter t + buyerUnitsAfter t
shareClassTransferPreservesIssuedSupply t =
  trans
    (cong (λ n → n + buyerUnitsBefore t) (sellerReconciled t))
    (trans
      (+-assoc (sellerUnitsAfter t) (transferredUnits t)
         (buyerUnitsBefore t))
      (trans
        (cong (sellerUnitsAfter t +_)
          (+-comm (transferredUnits t) (buyerUnitsBefore t)))
        (sym (cong (sellerUnitsAfter t +_) (buyerReconciled t)))))

twoOrdinarySharesTransferred : PureIssuedClassTransfer
twoOrdinarySharesTransferred =
  pure-issued-class-transfer 6 4 0 2 2 refl refl

sellerBuyerTotalIsConserved :
  sellerUnitsBefore twoOrdinarySharesTransferred
    + buyerUnitsBefore twoOrdinarySharesTransferred
  ≡ sellerUnitsAfter twoOrdinarySharesTransferred
    + buyerUnitsAfter twoOrdinarySharesTransferred
sellerBuyerTotalIsConserved =
  shareClassTransferPreservesIssuedSupply twoOrdinarySharesTransferred


------------------------------------------------------------------------
-- CONDITIONAL PHYSICAL STOCK/FLOW AND SERVICE THROUGHPUT (G04, G05).
-- Financial cash rights are NOT data of this record. This is a capacity
-- reconciliation requirement. It never asserts observed commissioning.
------------------------------------------------------------------------

record PhysicalCapacityPeriod : Set where
  constructor physical-capacity-period
  field
    installedBefore : Nat
    commissionedUnits : Nat
    retiredUnits : Nat
    installedAfter : Nat
    stockBalance :
      installedAfter + retiredUnits ≡ installedBefore + commissionedUnits
open PhysicalCapacityPeriod public

physicalCapitalStockFlowConservation :
  (period : PhysicalCapacityPeriod) →
  installedAfter period
    ≡ (installedBefore period + commissionedUnits period) ∸ retiredUnits period
physicalCapitalStockFlowConservation period =
  trans
    (sym (m+n∸n≡m (installedAfter period) (retiredUnits period)))
    (cong (_∸ retiredUnits period) (stockBalance period))

record DeliveredCareCapacity : Set where
  constructor delivered-care-capacity
  field
    actualStaffHours : Nat
    equipmentServiceHourCapacity : Nat
    actuallyDeliveredHours : Nat
    staffBound :
      actuallyDeliveredHours ≤ actualStaffHours
    equipmentBound :
      actuallyDeliveredHours ≤ equipmentServiceHourCapacity
open DeliveredCareCapacity public

deliveredCareHoursBoundedByStaffAndEquipment :
  (service : DeliveredCareCapacity) →
  actuallyDeliveredHours service ≤ actualStaffHours service
deliveredCareHoursBoundedByStaffAndEquipment service = staffBound service

deliveredCareHoursBoundedByEquipment :
  (service : DeliveredCareCapacity) →
  actuallyDeliveredHours service ≤ equipmentServiceHourCapacity service
deliveredCareHoursBoundedByEquipment service = equipmentBound service


------------------------------------------------------------------------
-- PARETO ORDER LAWS (I06): REUSE ORIGINAL MULTI-AXIS COST HYPERFABRIC.
-- We prove preorder laws over the existing weak-dominance definition;
-- admissibility, policy feasibility, and objective-axis choices remain
-- independently supplied by a real comparison consumer.
------------------------------------------------------------------------

paretoDominanceReflexive :
  {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  (candidate : Pareto.Model problem) →
  Pareto.WeaklyDominates costs candidate candidate
paretoDominanceReflexive costs candidate axis = ≤-refl

paretoDominanceTransitive :
  {problem : Pareto.ConsumerMDLProblem} →
  (costs : Pareto.CostHyperfabric problem) →
  {first second third : Pareto.Model problem} →
  Pareto.WeaklyDominates costs first second →
  Pareto.WeaklyDominates costs second third →
  Pareto.WeaklyDominates costs first third
paretoDominanceTransitive costs first≤second second≤third axis =
  ≤-trans (first≤second axis) (second≤third axis)

-- The order admits incomparable alternatives. It neither maximises a
-- scalar welfare score nor authorises a particular wealth-tax percentage.


------------------------------------------------------------------------
-- INCOMPARABLE FINITE POLICY OPTIONS: PARETO IS NOT A TOTAL RANKING.
-- The two outcomes are chosen synthetic *cost vectors*. They do not
-- represent enacted rates, measured welfare, or an empirical trade-off.
------------------------------------------------------------------------

data HypotheticalPolicyOutcome : Set where
  lowAdministrativeCost : HypotheticalPolicyOutcome
  increasedCareCapacity : HypotheticalPolicyOutcome

policyOutcomeProblem : Pareto.ConsumerMDLProblem
policyOutcomeProblem =
  Pareto.consumerMDLProblem
    HypotheticalPolicyOutcome
    (λ _ → ⊤)
    (λ _ → ⊤)
    (λ _ → 0)
    _≡_
    (λ _ → "synthetic-policy-outcome")
    "no code length used to rank outcomes"
    "hypothetical policy comparison only"

data PolicyTradeoffAxis : Set where
  administrationAxis : PolicyTradeoffAxis
  careShortfallAxis : PolicyTradeoffAxis

policyAxisCost : PolicyTradeoffAxis → HypotheticalPolicyOutcome → Nat
policyAxisCost administrationAxis lowAdministrativeCost = 0
policyAxisCost administrationAxis increasedCareCapacity = 5
policyAxisCost careShortfallAxis lowAdministrativeCost = 5
policyAxisCost careShortfallAxis increasedCareCapacity = 0

policyAxisReference : PolicyTradeoffAxis → String
policyAxisReference administrationAxis = "administrative-cost-units"
policyAxisReference careShortfallAxis = "missing-care-capacity-units"

policyTradeoffCosts : Pareto.CostHyperfabric policyOutcomeProblem
policyTradeoffCosts =
  Pareto.costHyperfabric PolicyTradeoffAxis policyAxisCost policyAxisReference

careOptionDoesNotDominateCheapAdministration :
  Pareto.WeaklyDominates policyTradeoffCosts
    increasedCareCapacity lowAdministrativeCost → ⊥
careOptionDoesNotDominateCheapAdministration dominance
  with dominance administrationAxis
... | ()

cheapAdministrationDoesNotDominateCareOption :
  Pareto.WeaklyDominates policyTradeoffCosts
    lowAdministrativeCost increasedCareCapacity → ⊥
cheapAdministrationDoesNotDominateCareOption dominance
  with dominance careShortfallAxis
... | ()

paretoOrderDoesNotTotallyRankTheseOptions :
  (Pareto.WeaklyDominates policyTradeoffCosts
     lowAdministrativeCost increasedCareCapacity
   ⊎ Pareto.WeaklyDominates policyTradeoffCosts
     increasedCareCapacity lowAdministrativeCost) → ⊥
paretoOrderDoesNotTotallyRankTheseOptions (inj₁ leftDominates) =
  cheapAdministrationDoesNotDominateCareOption leftDominates
paretoOrderDoesNotTotallyRankTheseOptions (inj₂ rightDominates) =
  careOptionDoesNotDominateCheapAdministration rightDominates

------------------------------------------------------------------------
-- 2026-10-28 FOLLOW-ON: BUDGET, ATTRIBUTION AND FINITE PARETO BOUNDARIES.
-- Model-conditional source terms, not externally observed transactions.
-- Original ASX/CHESS and empirical author ownership is unchanged.
------------------------------------------------------------------------

-- B06. A no-penalty/no-refund/no-interest collection is no greater than
-- the *named* assessed liability when the two exactly reconcile. The
-- assessment amount must be supplied by the caller; this does not
-- authenticate an assessment or exclude real statutory adjustments.
record NoAdjustmentCollection : Set where
  constructor no-adjustment-collection
  field
    assessedLiabilityUnits : Nat
    remittedPrincipalUnits : Nat
    stillUnpaidPrincipalUnits : Nat
    principalConservation :
      remittedPrincipalUnits + stillUnpaidPrincipalUnits
        ≡ assessedLiabilityUnits
open NoAdjustmentCollection public

remittanceBoundedByAssessedLiabilityUnderNoPenalties :
  (collection : NoAdjustmentCollection) →
  remittedPrincipalUnits collection ≤ assessedLiabilityUnits collection
remittanceBoundedByAssessedLiabilityUnderNoPenalties collection =
  subst
    (λ total → remittedPrincipalUnits collection ≤ total)
    (principalConservation collection)
    (m≤m+n (remittedPrincipalUnits collection)
      (stillUnpaidPrincipalUnits collection))

noAdjustmentCollectionExample : NoAdjustmentCollection
noAdjustmentCollectionExample =
  no-adjustment-collection 5 3 2 refl

-- B07. Avoid silently treating appropriation as actual expenditure.
-- The single budget identity includes distinct opening/other receipts,
-- administration, fiscal transfers, care appropriation and closing cash.
record ReconciledPublicCashBudget : Set where
  constructor reconciled-public-cash-budget
  field
    availablePublicCash : Nat
    administrativeCashOutflow : Nat
    transferCashOutflow : Nat
    careAppropriationCashOutflow : Nat
    retainedPublicCash : Nat
    publicCashBalance :
      availablePublicCash
        ≡ (administrativeCashOutflow + transferCashOutflow
            + careAppropriationCashOutflow) + retainedPublicCash
open ReconciledPublicCashBudget public

budgetOutflow : ReconciledPublicCashBudget → Nat
budgetOutflow budget =
  administrativeCashOutflow budget
    + transferCashOutflow budget + careAppropriationCashOutflow budget

cashBudgetConservationWithCostsAndTransfers :
  (budget : ReconciledPublicCashBudget) →
  budgetOutflow budget ≤ availablePublicCash budget
cashBudgetConservationWithCostsAndTransfers budget =
  subst
    (λ total → budgetOutflow budget ≤ total)
    (sym (publicCashBalance budget))
    (m≤m+n (budgetOutflow budget) (retainedPublicCash budget))

syntheticBalancedPublicBudget : ReconciledPublicCashBudget
syntheticBalancedPublicBudget =
  reconciled-public-cash-budget 9 1 2 3 3 refl

-- B08. Appropriating the same currency amount does not identify
-- delivered hours. The example is about missing information, not a
-- prediction that any named care institution delivers zero hours.
record CareDeliveryCounterworld : Set where
  constructor care-delivery-counterworld
  field
    careAppropriationAmount : Nat
    deliveredCareServiceHours : Nat
open CareDeliveryCounterworld public

fundedUnstaffedCare : CareDeliveryCounterworld
fundedUnstaffedCare = care-delivery-counterworld 2 0

fundedStaffedCare : CareDeliveryCounterworld
fundedStaffedCare = care-delivery-counterworld 2 1

differentCareHoursAtSameAppropriation :
  deliveredCareServiceHours fundedUnstaffedCare
    ≡ deliveredCareServiceHours fundedStaffedCare → ⊥
differentCareHoursAtSameAppropriation ()

careAppropriatedDoesNotDetermineCareDelivered :
  INF.FactorsThrough careAppropriationAmount deliveredCareServiceHours → ⊥
careAppropriatedDoesNotDetermineCareDelivered =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      fundedUnstaffedCare fundedStaffedCare refl
      differentCareHoursAtSameAppropriation)

-- C09 partial: an arithmetically balanced source route is not a proof
-- that financing or settlement was accessible at remittance time.
-- A real feasibility determination needs external liquidity, collateral
-- and time evidence. Bool here is an *assumption*, not a broker receipt.
record RouteAccessCounterworld : Set where
  constructor route-access-counterworld
  field
    attemptedRoute : FundingRoute
    externalFundsAccessible : Bool
open RouteAccessCounterworld public

accessibleSyntheticRoute : RouteAccessCounterworld
accessibleSyntheticRoute =
  route-access-counterworld assetSaleFunded true

inaccessibleSyntheticRoute : RouteAccessCounterworld
inaccessibleSyntheticRoute =
  route-access-counterworld assetSaleFunded false

identicalRouteCashReceipt : RouteAccessCounterworld → Nat
identicalRouteCashReceipt world =
  taxPaymentForRoute (attemptedRoute world)

routeBalanceDoesNotEstablishLiquidityOrTiming :
  INF.FactorsThrough identicalRouteCashReceipt externalFundsAccessible → ⊥
routeBalanceDoesNotEstablishLiquidityOrTiming =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      accessibleSyntheticRoute inaccessibleSyntheticRoute refl
      (λ ()))

-- F06. A participant's cash batch is not an authenticated beneficial
-- owner. Synthetic identifier numbers are *distinguishable fixture keys*,
-- not legal, brokerage, HIN, or custody-verified identities.
record ParticipantIdentityCounterworld : Set where
  constructor participant-identity-counterworld
  field
    participantClearing : ParticipantClearingBatch
    unverifiedInvestorKey : Nat
open ParticipantIdentityCounterworld public

participantNetCashProjection : ParticipantIdentityCounterworld → Nat
participantNetCashProjection world =
  netReceivedCash (participantClearing world)

firstAttributionCandidate : ParticipantIdentityCounterworld
firstAttributionCandidate =
  participant-identity-counterworld offsettingClearedTransactions 1

secondAttributionCandidate : ParticipantIdentityCounterworld
secondAttributionCandidate =
  participant-identity-counterworld offsettingClearedTransactions 2

differentInvestorKeysDespiteMatchingNet :
  unverifiedInvestorKey firstAttributionCandidate
    ≡ unverifiedInvestorKey secondAttributionCandidate → ⊥
differentInvestorKeysDespiteMatchingNet ()

participantNetStatementDoesNotIdentifyIndividualTaxpayer :
  INF.FactorsThrough participantNetCashProjection unverifiedInvestorKey → ⊥
participantNetStatementDoesNotIdentifyIndividualTaxpayer =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      firstAttributionCandidate secondAttributionCandidate refl
      differentInvestorKeysDespiteMatchingNet)

-- G06 partial: conditional resource constraints, never a conversion
-- from money, votes or traded shares to material productive output.
record FixedInputConstructionFeasibility : Set where
  constructor fixed-input-construction-feasibility
  field
    commissionedPlantUnits : Nat
    energyPerPlantUnit : Nat
    materialPerPlantUnit : Nat
    physicallyAvailableEnergy : Nat
    physicallyAvailableMaterials : Nat
    energySufficesForConstruction :
      commissionedPlantUnits * energyPerPlantUnit ≤ physicallyAvailableEnergy
    materialsSufficeForConstruction :
      commissionedPlantUnits * materialPerPlantUnit
        ≤ physicallyAvailableMaterials
open FixedInputConstructionFeasibility public

energyMaterialsAndConstructionRequireSeparateInputs :
  (period : FixedInputConstructionFeasibility) →
  (commissionedPlantUnits period * energyPerPlantUnit period
    ≤ physicallyAvailableEnergy period)
  × (commissionedPlantUnits period * materialPerPlantUnit period
    ≤ physicallyAvailableMaterials period)
energyMaterialsAndConstructionRequireSeparateInputs period =
  energySufficesForConstruction period ,
  materialsSufficeForConstruction period

-- I08 finite countermodel. A *pair* of incomparable alternatives can
-- both be Pareto-minimal. This does NOT construct a full finite-frontier
-- algorithm (I07), set a tax rate or select a welfare function.
TwoOptionUndominated : HypotheticalPolicyOutcome → Set
TwoOptionUndominated candidate =
  (challenger : HypotheticalPolicyOutcome) →
    Pareto.WeaklyDominates policyTradeoffCosts challenger candidate →
    Pareto.WeaklyDominates policyTradeoffCosts candidate challenger

cheapAdministrationIsUndominated : TwoOptionUndominated lowAdministrativeCost
cheapAdministrationIsUndominated lowAdministrativeCost _ =
  paretoDominanceReflexive policyTradeoffCosts lowAdministrativeCost
cheapAdministrationIsUndominated increasedCareCapacity challengerDominates
  with careOptionDoesNotDominateCheapAdministration challengerDominates
... | ()

careCapacityIsUndominated : TwoOptionUndominated increasedCareCapacity
careCapacityIsUndominated lowAdministrativeCost challengerDominates
  with cheapAdministrationDoesNotDominateCareOption challengerDominates
... | ()
careCapacityIsUndominated increasedCareCapacity _ =
  paretoDominanceReflexive policyTradeoffCosts increasedCareCapacity

careAndAdministrationAreDistinct :
  increasedCareCapacity ≡ lowAdministrativeCost → ⊥
careAndAdministrationAreDistinct ()

finiteParetoTradeoffHasTwoDistinctMinimalOptions :
  TwoOptionUndominated lowAdministrativeCost
  × TwoOptionUndominated increasedCareCapacity
finiteParetoTradeoffHasTwoDistinctMinimalOptions =
  cheapAdministrationIsUndominated , careCapacityIsUndominated

paretoMinimalityCannotUniquelySelectCheapAdministration :
  ((candidate : HypotheticalPolicyOutcome) →
    TwoOptionUndominated candidate →
    candidate ≡ lowAdministrativeCost) → ⊥
paretoMinimalityCannotUniquelySelectCheapAdministration unique =
  careAndAdministrationAreDistinct
    (unique increasedCareCapacity careCapacityIsUndominated)

------------------------------------------------------------------------
-- D12 FINITE FILL TOKEN UNIQUENESS + PER-FILL CHRONOLOGY.
-- All timestamps are caller-supplied ordered integers; no timezone,
-- exchange calendar, signed execution report or custody identity follows.
-- Security-class labels are explicit but unauthenticated local strings.
------------------------------------------------------------------------

record TimestampedFill : Set where
  constructor timestamped-fill
  field
    localFillToken : Nat
    fillIssuerLabel : String
    fillClassLabel : String
    submissionEpoch : Nat
    executionEpoch : Nat
    clearingEpoch : Nat
    settlementEpoch : Nat
    submittedBeforeExecuted : submissionEpoch ≤ executionEpoch
    executedBeforeCleared : executionEpoch ≤ clearingEpoch
    clearedBeforeSettled : clearingEpoch ≤ settlementEpoch
open TimestampedFill public

-- No duplicate *local token* is permitted anywhere in an arbitrary finite
-- batch. The record enforces individual event chronology. It does not
-- assert consecutive fills arrived in timestamp-sorted list order.
TokenAbsent : Nat → List TimestampedFill → Set
TokenAbsent token [] = ⊤
TokenAbsent token (fill ∷ rest) =
  (token ≡ localFillToken fill → ⊥) × TokenAbsent token rest

UniqueFillTokens : List TimestampedFill → Set
UniqueFillTokens [] = ⊤
UniqueFillTokens (fill ∷ rest) =
  TokenAbsent (localFillToken fill) rest × UniqueFillTokens rest

AllFillLabelsMatch : String → String → List TimestampedFill → Set
AllFillLabelsMatch issuer security [] = ⊤
AllFillLabelsMatch issuer security (fill ∷ rest) =
  (issuer ≡ fillIssuerLabel fill)
    × ((security ≡ fillClassLabel fill)
       × AllFillLabelsMatch issuer security rest)

record ChronologicalIdentifiedFillBatch : Set where
  constructor chronological-identified-fill-batch
  field
    requestedIssuerLabel : String
    requestedSecurityClassLabel : String
    timestampedFills : List TimestampedFill
    uniqueLocalTokens : UniqueFillTokens timestampedFills
    reconciledIssuerClassLabels :
      AllFillLabelsMatch requestedIssuerLabel
        requestedSecurityClassLabel timestampedFills
open ChronologicalIdentifiedFillBatch public

uniqueFillIdentityAndMonotoneEventTime :
  (batch : ChronologicalIdentifiedFillBatch) →
  UniqueFillTokens (timestampedFills batch)
  × AllFillLabelsMatch
      (requestedIssuerLabel batch) (requestedSecurityClassLabel batch)
      (timestampedFills batch)
uniqueFillIdentityAndMonotoneEventTime batch =
  uniqueLocalTokens batch , reconciledIssuerClassLabels batch

-- Two equal-valued fills with the *same* local ID cannot satisfy the
-- finite-list uniqueness contract. This is a negative fixture only.
syntheticFill7 : TimestampedFill
syntheticFill7 =
  timestamped-fill 7 "fixture-issuer" "fixture-ordinary"
    1 1 1 1 ≤-refl ≤-refl ≤-refl

syntheticFill8 : TimestampedFill
syntheticFill8 =
  timestamped-fill 8 "fixture-issuer" "fixture-ordinary"
    1 1 1 1 ≤-refl ≤-refl ≤-refl

duplicateSevenTokenRejected :
  UniqueFillTokens (syntheticFill7 ∷ syntheticFill7 ∷ []) → ⊥
duplicateSevenTokenRejected ((notSameToken , _) , _) =
  notSameToken refl

sevenAndEightTokensAreDistinct : 7 ≡ 8 → ⊥
sevenAndEightTokensAreDistinct ()

twoDistinctTokensAreUnique :
  UniqueFillTokens (syntheticFill7 ∷ syntheticFill8 ∷ [])
twoDistinctTokensAreUnique =
  (sevenAndEightTokensAreDistinct , tt) , (tt , tt)

twoFillLabelsAgree :
  AllFillLabelsMatch "fixture-issuer" "fixture-ordinary"
    (syntheticFill7 ∷ syntheticFill8 ∷ [])
twoFillLabelsAgree =
  refl , (refl , (refl , (refl , tt)))

twoIdentifiedChronologicalFills : ChronologicalIdentifiedFillBatch
twoIdentifiedChronologicalFills =
  chronological-identified-fill-batch
    "fixture-issuer" "fixture-ordinary"
    (syntheticFill7 ∷ syntheticFill8 ∷ [])
    twoDistinctTokensAreUnique twoFillLabelsAgree

-- Even a structurally valid finite list is not an authenticated broker,
-- exchange, nominee/custodian or ASX settlement allocation receipt.

------------------------------------------------------------------------
-- D11 × D12 SAME-SEQUENCE REFINEMENT.
-- A separate list of unique tokens cannot certify the cash fills unless
-- the *entire ordered price/quantity projection* is explicitly matched.
-- This is local list equality, not broker/custody historical authentication.
------------------------------------------------------------------------

record JoinedPriceIdentityFill : Set where
  constructor joined-price-identity-fill
  field
    timedPart : TimestampedFill
    pricedPart : PriceQuantityFill
open JoinedPriceIdentityFill public

pricedProjection : List JoinedPriceIdentityFill → List PriceQuantityFill
pricedProjection [] = []
pricedProjection (fill ∷ rest) =
  pricedPart fill ∷ pricedProjection rest

timedProjection : List JoinedPriceIdentityFill → List TimestampedFill
timedProjection [] = []
timedProjection (fill ∷ rest) =
  timedPart fill ∷ timedProjection rest

record JoinedPriceIdentityBatch : Set where
  constructor joined-price-identity-batch
  field
    settledCashBatch : CashReconciledFillBatch
    joinedFills : List JoinedPriceIdentityFill
    issuerOfJoinedBatch : String
    classOfJoinedBatch : String
    fullPriceSequenceMatched :
      pricedProjection joinedFills ≡ settledFills settledCashBatch
    distinctJoinedTokens : UniqueFillTokens (timedProjection joinedFills)
    allJoinedLabelsMatched :
      AllFillLabelsMatch issuerOfJoinedBatch classOfJoinedBatch
        (timedProjection joinedFills)
open JoinedPriceIdentityBatch public

joinedIdentityAndCashReconcile :
  (batch : JoinedPriceIdentityBatch) →
  recordedGrossCash (settledCashBatch batch)
    ≡ grossFromFiniteSettledFills (pricedProjection (joinedFills batch))
  × UniqueFillTokens (timedProjection (joinedFills batch))
joinedIdentityAndCashReconcile batch =
  trans
    (settledProceedsMatchRecordedCash (settledCashBatch batch))
    (cong grossFromFiniteSettledFills
      (sym (fullPriceSequenceMatched batch))) ,
  distinctJoinedTokens batch

syntheticPriceIdentityBatch : JoinedPriceIdentityBatch
syntheticPriceIdentityBatch =
  joined-price-identity-batch
    twoFillGenericWitness
    (joined-price-identity-fill syntheticFill7 (price-quantity-fill 1 1)
      ∷ joined-price-identity-fill syntheticFill8 (price-quantity-fill 1 2)
      ∷ [])
    "fixture-issuer" "fixture-ordinary"
    refl twoDistinctTokensAreUnique twoFillLabelsAgree

syntheticJoinedTwoFillCash :
  recordedGrossCash (settledCashBatch syntheticPriceIdentityBatch) ≡ 3
syntheticJoinedTwoFillCash = refl

-- Even this exact sequence reconciliation cannot prove that the original
-- broker issued these IDs, the buyer received title, the seller funded a
-- prior tax liability or any named investor owns a real voting share.

------------------------------------------------------------------------
-- 2026-10-28 SECOND FOLLOW-ON: STOCK, EVIDENCE AND RIVAL POLICIES.
-- These are hypothetical, conditional Agda source constructions.
-- They do not mint original tax assessments, brokerage credentials,
-- issuer registers, economic observations or official settlement receipts.
------------------------------------------------------------------------

-- A05. Consistent accounting unit and instant are coordinates of a
-- supplied snapshot; ownership and valuation must be verified elsewhere.
record ScopedNetWealthSnapshot : Set where
  constructor scoped-net-wealth-snapshot
  field
    assessmentEpoch : Nat
    monetaryUnitLabel : String
    declaredGrossUnits : Nat
    excludedAssetsUnits : Nat
    includedAssetsUnits : Nat
    liabilityUnits : Nat
    calculatedNetWealthUnits : Nat
    exclusionsReconciled :
      includedAssetsUnits + excludedAssetsUnits ≡ declaredGrossUnits
    netAssetDebtReconciled :
      calculatedNetWealthUnits + liabilityUnits ≡ includedAssetsUnits
open ScopedNetWealthSnapshot public

netWealthBalanceIsWellTyped :
  (snapshot : ScopedNetWealthSnapshot) →
  (includedAssetsUnits snapshot + excludedAssetsUnits snapshot
    ≡ declaredGrossUnits snapshot)
  × (calculatedNetWealthUnits snapshot + liabilityUnits snapshot
    ≡ includedAssetsUnits snapshot)
netWealthBalanceIsWellTyped snapshot =
  exclusionsReconciled snapshot , netAssetDebtReconciled snapshot

illustrativeNetWealthSnapshot : ScopedNetWealthSnapshot
illustrativeNetWealthSnapshot =
  scoped-net-wealth-snapshot 1 "hypothetical-currency-unit" 12 2 10 3 7 refl refl

-- C08. Reuse the existing E06 owner. A transfer of already-issued
-- ownership claims does not, by its arithmetic alone, retire machines.
-- The plant identity must be supplied independently.
record TransferWithUnalteredPlant : Set where
  constructor transfer-with-unaltered-plant
  field
    shareHandoff : PureIssuedClassTransfer
    plantBeforeHandoff : Nat
    plantAfterHandoff : Nat
    plantUnalteredByHandoff :
      plantAfterHandoff ≡ plantBeforeHandoff
open TransferWithUnalteredPlant public

disposalPreservesExternalAssetTransferAccounting :
  (handoff : TransferWithUnalteredPlant) →
  (sellerUnitsBefore (shareHandoff handoff)
     + buyerUnitsBefore (shareHandoff handoff)
     ≡ sellerUnitsAfter (shareHandoff handoff)
       + buyerUnitsAfter (shareHandoff handoff))
  × (plantAfterHandoff handoff ≡ plantBeforeHandoff handoff)
disposalPreservesExternalAssetTransferAccounting handoff =
  shareClassTransferPreservesIssuedSupply (shareHandoff handoff) ,
  plantUnalteredByHandoff handoff

-- E08. Majority arithmetic cannot determine contractual control.
-- The second axis is an EXTERNAL ASSUMPTION, not an actual AASB 10 verdict.
record ControlEvidenceWorld : Set where
  constructor control-evidence-world
  field
    arithmeticVotes : Nat
    externallyAssumedEffectiveControl : Bool
open ControlEvidenceWorld public

sameVotesControlA : ControlEvidenceWorld
sameVotesControlA = control-evidence-world 34 true

sameVotesControlB : ControlEvidenceWorld
sameVotesControlB = control-evidence-world 34 false

effectiveControlDiffersWithIdenticalVotes :
  externallyAssumedEffectiveControl sameVotesControlA
    ≡ externallyAssumedEffectiveControl sameVotesControlB → ⊥
effectiveControlDiffersWithIdenticalVotes ()

controllingVotesRequireVerifiedRightsAndAgreements :
  INF.FactorsThrough arithmeticVotes externallyAssumedEffectiveControl → ⊥
controllingVotesRequireVerifiedRightsAndAgreements =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameVotesControlA sameVotesControlB refl
      effectiveControlDiffersWithIdenticalVotes)

-- E09. Equal local digest values do not establish historical event identity.
-- These are synthetic NUMERIC LABELS. This is NOT a cryptographic
-- SHA-256 collision claim, and no actual registry identity is created.
record DigestEventCounterworld : Set where
  constructor digest-event-counterworld
  field
    arbitraryDigestLabel : Nat
    distinctHistoricalEventLabel : Nat
open DigestEventCounterworld public

digestWorldA : DigestEventCounterworld
digestWorldA = digest-event-counterworld 7 11

digestWorldB : DigestEventCounterworld
digestWorldB = digest-event-counterworld 7 12

differentEventsWithEqualDigestLabel :
  distinctHistoricalEventLabel digestWorldA
    ≡ distinctHistoricalEventLabel digestWorldB → ⊥
differentEventsWithEqualDigestLabel ()

persistentTransactionIdentityCannotFollowFromValueOrDigest :
  INF.FactorsThrough arbitraryDigestLabel distinctHistoricalEventLabel → ⊥
persistentTransactionIdentityCannotFollowFromValueOrDigest =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      digestWorldA digestWorldB refl differentEventsWithEqualDigestLabel)

-- F07. A separate externally checked authority witness must accompany
-- source-certified settlement. A synthetic SingleInstrumentDvPBatch
-- alone does not generate a term of OfficialReceiptValid.
record OfficialSettlementAdmission
    (OfficialReceipt : Set)
    (OfficialReceiptValid : OfficialReceipt → Set) : Set where
  constructor official-settlement-admission
  field
    settlementSimulation : SingleInstrumentDvPBatch
    independentOfficialReceipt : OfficialReceipt
    independentAuthorityCheck :
      OfficialReceiptValid independentOfficialReceipt
open OfficialSettlementAdmission public

actualSettlementFinalityRequiresOfficialReceipt :
  {OfficialReceipt : Set} →
  {OfficialReceiptValid : OfficialReceipt → Set} →
  (admission : OfficialSettlementAdmission OfficialReceipt OfficialReceiptValid) →
  OfficialReceiptValid (independentOfficialReceipt admission)
actualSettlementFinalityRequiresOfficialReceipt = independentAuthorityCheck

-- G07. Model a financial claim position and a distinct productive output.
-- Sharing one balance cannot recover the physical measurement.
record FinancePhysicalObservation : Set where
  constructor finance-physical-observation
  field
    investorFinancialClaimUnits : Nat
    physicalOutputUnits : Nat
open FinancePhysicalObservation public

financePhysicalA : FinancePhysicalObservation
financePhysicalA = finance-physical-observation 5 0

financePhysicalB : FinancePhysicalObservation
financePhysicalB = finance-physical-observation 5 2

physicalOutputDiffersAtSameClaim :
  physicalOutputUnits financePhysicalA
    ≡ physicalOutputUnits financePhysicalB → ⊥
physicalOutputDiffersAtSameClaim ()

financialClaimChangeDoesNotIdentifyPhysicalOutput :
  INF.FactorsThrough investorFinancialClaimUnits physicalOutputUnits → ⊥
financialClaimChangeDoesNotIdentifyPhysicalOutput =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      financePhysicalA financePhysicalB refl
      physicalOutputDiffersAtSameClaim)

-- I01. Reuse the original Base.TaxBase and its taxBase interpretation.
-- A common numeric measurement unit makes two policies comparable on a
-- chosen axis but does not erase the different taxable legal object.
record RivalTaxBaseComparison : Set where
  constructor rival-tax-base-comparison
  field
    firstPolicy : Tax.Policy
    secondPolicy : Tax.Policy
    firstTaxBase : Tax.TaxBase
    secondTaxBase : Tax.TaxBase
    firstBaseReconciles : firstTaxBase ≡ Tax.taxBase firstPolicy
    secondBaseReconciles : secondTaxBase ≡ Tax.taxBase secondPolicy
    firstPolicyCost : Nat
    secondPolicyCost : Nat
    comparativeCostUnit : String
open RivalTaxBaseComparison public

rivalPolicyTaxBasesRemainComparableButDistinct :
  (pair : RivalTaxBaseComparison) →
  (firstTaxBase pair ≡ Tax.taxBase (firstPolicy pair))
  × (secondTaxBase pair ≡ Tax.taxBase (secondPolicy pair))
rivalPolicyTaxBasesRemainComparableButDistinct pair =
  firstBaseReconciles pair , secondBaseReconciles pair

illustrativeIncomeWealthComparison : RivalTaxBaseComparison
illustrativeIncomeWealthComparison =
  rival-tax-base-comparison
    Tax.incomeHundredAboveThreshold
    Tax.wealthHundredAboveThreshold
    Tax.annualPersonalIncome
    Tax.currentNetWealth
    refl refl 2 2 "illustrative-cost-units"

-- I02. A proposal has no statutory standing just because it has an
-- illustrative cost. An enacted tag needs an independently checked
-- enactment record. This interface cannot manufacture that record.
data PolicyAuthorityMode : Set where
  hypotheticalOnly : PolicyAuthorityMode
  statutoryEvidenceRequired : PolicyAuthorityMode

record TaggedPolicyScenario : Set where
  constructor tagged-policy-scenario
  field
    representedPolicy : Tax.Policy
    authorityMode : PolicyAuthorityMode
    policyReference : String
open TaggedPolicyScenario public

record StatutoryPolicyAdmission
    (LegalRecord : Set)
    (ValidApplicableStatute : LegalRecord → Set) : Set where
  constructor statutory-policy-admission
  field
    claimedEnactedScenario : TaggedPolicyScenario
    enactedTagRequired :
      authorityMode claimedEnactedScenario ≡ statutoryEvidenceRequired
    independentLegalRecord : LegalRecord
    originalStatuteChecked :
      ValidApplicableStatute independentLegalRecord
open StatutoryPolicyAdmission public

policyScenarioRequiresStatuteOrHypotheticalTag :
  (scenario : TaggedPolicyScenario) →
  PolicyAuthorityMode
policyScenarioRequiresStatuteOrHypotheticalTag = authorityMode

-- I03. A period transition carries exact modeled stock conservation
-- independently of any policy prediction or real-world valuation.
record FinitePolicyAccountingPeriod : Set where
  constructor finite-policy-accounting-period
  field
    assetStockBefore : Nat
    receivedRealResources : Nat
    transferredAwayResources : Nat
    assetStockAfter : Nat
    finiteStockFlowReconciled :
      assetStockAfter + transferredAwayResources
        ≡ assetStockBefore + receivedRealResources
open FinitePolicyAccountingPeriod public

finitePolicyStateTransitionPreservesAccounting :
  (period : FinitePolicyAccountingPeriod) →
  assetStockAfter period + transferredAwayResources period
    ≡ assetStockBefore period + receivedRealResources period
finitePolicyStateTransitionPreservesAccounting = finiteStockFlowReconciled

-- I04. Migration / credit / trading response coefficients are assumed
-- parameters, not universally identified from the tax base.
record ExplicitBehaviourAssumptions : Set where
  constructor explicit-behaviour-assumptions
  field
    migrationResponseNumerator : Nat
    migrationResponseDenominator : Nat
    creditAccessResponseNumerator : Nat
    creditAccessResponseDenominator : Nat
    slowPortfolioAdjustmentPeriods : Nat
    sourceAssumptionReference : String
open ExplicitBehaviourAssumptions public

behaviouralResponseParametersAreExplicitAssumptions :
  (assumptions : ExplicitBehaviourAssumptions) →
  Nat
behaviouralResponseParametersAreExplicitAssumptions =
  slowPortfolioAdjustmentPeriods

-- I05. Holding initial state equal is a separate reconciled premise.
-- A paired scenario is NOT an observed counterfactual study.
record SharedInitialPolicyComparison : Set where
  constructor shared-initial-policy-comparison
  field
    baselineScenario : TaggedPolicyScenario
    interventionScenario : TaggedPolicyScenario
    baselineOpeningWealth : Nat
    interventionOpeningWealth : Nat
    initialStatesMatched :
      baselineOpeningWealth ≡ interventionOpeningWealth
open SharedInitialPolicyComparison public

sameInitialStateDifferentInterventionComparison :
  (comparison : SharedInitialPolicyComparison) →
  baselineOpeningWealth comparison ≡ interventionOpeningWealth comparison
sameInitialStateDifferentInterventionComparison =
  initialStatesMatched

-- I09. Two worlds have the same synthetic forecast but distinct observed
-- coordinates. Synthetic predictions do not identify actual outcomes.
-- The observed coordinate here is an illustrative counterworld value,
-- NOT collected or observed tax data.
record SimulatedVsExternalOutcomeWorld : Set where
  constructor simulated-vs-external-outcome-world
  field
    modelPredictionUnits : Nat
    independentlySuppliedOutcomeUnits : Nat
open SimulatedVsExternalOutcomeWorld public

syntheticVersusExternalA : SimulatedVsExternalOutcomeWorld
syntheticVersusExternalA = simulated-vs-external-outcome-world 4 0

syntheticVersusExternalB : SimulatedVsExternalOutcomeWorld
syntheticVersusExternalB = simulated-vs-external-outcome-world 4 1

externalOutcomeDiffersAtSamePrediction :
  independentlySuppliedOutcomeUnits syntheticVersusExternalA
    ≡ independentlySuppliedOutcomeUnits syntheticVersusExternalB → ⊥
externalOutcomeDiffersAtSamePrediction ()

syntheticModelCannotIdentifyObservedCausalEffect :
  INF.FactorsThrough modelPredictionUnits independentlySuppliedOutcomeUnits → ⊥
syntheticModelCannotIdentifyObservedCausalEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      syntheticVersusExternalA syntheticVersusExternalB refl
      externalOutcomeDiffersAtSamePrediction)

------------------------------------------------------------------------
-- 2026-10-28 THIRD FOLLOW-ON: EXCLUSIVE SOURCE TAGS AND MATCHED ADMISSION.
-- Inputs bearing the word "authenticated" require an external checker;
-- no local label, hash or record constructor supplies that checker.
------------------------------------------------------------------------

-- C06. An individual funding source contributes to exactly one channel.
-- Repetition of a historical source with a forged new local token is NOT
-- prevented by the type; genuine source identity is an external obligation.
data ExclusiveFundingChannel : Set where
  existingCashChannel : ExclusiveFundingChannel
  freshLoanChannel : ExclusiveFundingChannel
  settledSaleChannel : ExclusiveFundingChannel

record TaggedFundingReceipt : Set where
  constructor tagged-funding-receipt
  field
    fundingSourceToken : Nat
    fundingSourceChannel : ExclusiveFundingChannel
    fundingSourceUnits : Nat
open TaggedFundingReceipt public

cashContribution : TaggedFundingReceipt → Nat
cashContribution (tagged-funding-receipt _ existingCashChannel n) = n
cashContribution (tagged-funding-receipt _ freshLoanChannel n) = zero
cashContribution (tagged-funding-receipt _ settledSaleChannel n) = zero

loanContribution : TaggedFundingReceipt → Nat
loanContribution (tagged-funding-receipt _ existingCashChannel n) = zero
loanContribution (tagged-funding-receipt _ freshLoanChannel n) = n
loanContribution (tagged-funding-receipt _ settledSaleChannel n) = zero

saleContribution : TaggedFundingReceipt → Nat
saleContribution (tagged-funding-receipt _ existingCashChannel n) = zero
saleContribution (tagged-funding-receipt _ freshLoanChannel n) = zero
saleContribution (tagged-funding-receipt _ settledSaleChannel n) = n

cashSourceUseIsSingleCounted :
  (source : TaggedFundingReceipt) →
  (cashContribution source + loanContribution source)
    + saleContribution source ≡ fundingSourceUnits source
cashSourceUseIsSingleCounted (tagged-funding-receipt _ existingCashChannel n) =
  refl
cashSourceUseIsSingleCounted (tagged-funding-receipt _ freshLoanChannel n) =
  refl
cashSourceUseIsSingleCounted (tagged-funding-receipt _ settledSaleChannel n) =
  refl

-- C09 conditional route admission. The positive conclusion requires
-- credit, liquidity and chronology proofs, supplied independently.
record FinancedRouteAdmission : Set where
  constructor financed-route-admission
  field
    admittedFundingRoute : FundingRoute
    availableLiquidCash : Nat
    unrestrictedCashWithinLiquidity :
      unrestrictedCash admittedFundingRoute ≤ availableLiquidCash
    supportedCreditLimit : Nat
    lendingWithinCollateralLimit :
      newLoanCash admittedFundingRoute ≤ supportedCreditLimit
    lastSettlementEpoch : Nat
    taxPaymentEpoch : Nat
    fundedBeforeRemittance :
      lastSettlementEpoch ≤ taxPaymentEpoch
open FinancedRouteAdmission public

routeFundingFeasibleGivenLiquidityCollateralAndTiming :
  (receipt : FinancedRouteAdmission) →
  (unrestrictedCash (admittedFundingRoute receipt)
    ≤ availableLiquidCash receipt)
  × ((newLoanCash (admittedFundingRoute receipt)
    ≤ supportedCreditLimit receipt)
     × (lastSettlementEpoch receipt ≤ taxPaymentEpoch receipt))
routeFundingFeasibleGivenLiquidityCollateralAndTiming receipt =
  unrestrictedCashWithinLiquidity receipt ,
  (lendingWithinCollateralLimit receipt , fundedBeforeRemittance receipt)

-- E07. Source-checked holder and issuer/class matching must come from
-- an independently validated registry receipt. String field agreement
-- does not verify legal title, beneficial ownership or real signatures.
record OwnerIssuerSecurityAdmission
    (OfficialRegistryReceipt : Set)
    (RegistryValid : OfficialRegistryReceipt → Set) : Set where
  constructor owner-issuer-security-admission
  field
    ownershipRegisterReceipt : OfficialRegistryReceipt
    independentRegistryValidation :
      RegistryValid ownershipRegisterReceipt
    namedInvestorAtFill : String
    namedInvestorOnRegister : String
    namedIssuerAtFill : String
    namedIssuerOnRegister : String
    namedShareClassAtFill : String
    namedShareClassOnRegister : String
    sameNamedInvestor :
      namedInvestorAtFill ≡ namedInvestorOnRegister
    sameNamedIssuer :
      namedIssuerAtFill ≡ namedIssuerOnRegister
    sameNamedShareClass :
      namedShareClassAtFill ≡ namedShareClassOnRegister
open OwnerIssuerSecurityAdmission public

authenticatedOwnerIssuerInstrumentClassKey :
  {OfficialRegistryReceipt : Set} →
  {RegistryValid : OfficialRegistryReceipt → Set} →
  (admission : OwnerIssuerSecurityAdmission
    OfficialRegistryReceipt RegistryValid) →
  RegistryValid (ownershipRegisterReceipt admission)
  × ((namedInvestorAtFill admission ≡ namedInvestorOnRegister admission)
      × ((namedIssuerAtFill admission ≡ namedIssuerOnRegister admission)
          × (namedShareClassAtFill admission ≡ namedShareClassOnRegister admission)))
authenticatedOwnerIssuerInstrumentClassKey admission =
  independentRegistryValidation admission ,
  (sameNamedInvestor admission ,
    (sameNamedIssuer admission , sameNamedShareClass admission))

-- H08. Independent authority, same-object custody/assessment keys,
-- and a causal identification predicate are separate inputs.
-- No inhabited external authoritative evidence is fabricated here.
record MatchedPolicyEffectAdmission
    (AssessmentRecord CustodyRecord OutcomeRecord DesignRecord : Set)
    (AssessmentVerified : AssessmentRecord → Set)
    (CustodyVerified : CustodyRecord → Set)
    (OutcomeVerified : OutcomeRecord → Set)
    (DesignVerified : DesignRecord → Set) : Set where
  constructor matched-policy-effect-admission
  field
    primaryTaxAssessment : AssessmentRecord
    taxAssessmentChecked : AssessmentVerified primaryTaxAssessment
    primaryCustodyMovement : CustodyRecord
    custodyMovementChecked : CustodyVerified primaryCustodyMovement
    primaryPhysicalOutcome : OutcomeRecord
    outcomeChecked : OutcomeVerified primaryPhysicalOutcome
    independentCausalDesign : DesignRecord
    causalDesignChecked : DesignVerified independentCausalDesign
    taxSourceTaxpayerKey : Nat
    custodyTaxpayerKey : Nat
    assessmentAndCustodySamePerson :
      taxSourceTaxpayerKey ≡ custodyTaxpayerKey
    custodySecurityKey : Nat
    outcomeSecurityKey : Nat
    custodyAndOutcomeSameSecurity :
      custodySecurityKey ≡ outcomeSecurityKey
open MatchedPolicyEffectAdmission public

measuredPolicyEffectRequiresSameObjectInputs :
  {AssessmentRecord CustodyRecord OutcomeRecord DesignRecord : Set} →
  {AssessmentVerified : AssessmentRecord → Set} →
  {CustodyVerified : CustodyRecord → Set} →
  {OutcomeVerified : OutcomeRecord → Set} →
  {DesignVerified : DesignRecord → Set} →
  (joined : MatchedPolicyEffectAdmission
    AssessmentRecord CustodyRecord OutcomeRecord DesignRecord
    AssessmentVerified CustodyVerified OutcomeVerified DesignVerified) →
  (taxSourceTaxpayerKey joined ≡ custodyTaxpayerKey joined)
    × (custodySecurityKey joined ≡ outcomeSecurityKey joined)
measuredPolicyEffectRequiresSameObjectInputs joined =
  assessmentAndCustodySamePerson joined ,
  custodyAndOutcomeSameSecurity joined

-- I08. Two explicit, hypothetical tax-rate labels can each sit behind
-- a non-dominated outcome. Pareto alone cannot uniquely SELECT the rate.
-- These labels are illustrative, not enacted rates or rate advice.
data SyntheticRateLabel : Set where
  exampleZeroRate : SyntheticRateLabel
  exampleFullExcessRate : SyntheticRateLabel

rateTagForOutcome : HypotheticalPolicyOutcome → SyntheticRateLabel
rateTagForOutcome lowAdministrativeCost = exampleZeroRate
rateTagForOutcome increasedCareCapacity = exampleFullExcessRate

syntheticTaxRateLabelsAreDifferent :
  exampleFullExcessRate ≡ exampleZeroRate → ⊥
syntheticTaxRateLabelsAreDifferent ()

noUniqueOptimalTaxRateFromParetoOrderAlone :
  ((candidate : HypotheticalPolicyOutcome) →
    TwoOptionUndominated candidate →
    rateTagForOutcome candidate ≡ exampleZeroRate) → ⊥
noUniqueOptimalTaxRateFromParetoOrderAlone claimedUnique =
  syntheticTaxRateLabelsAreDifferent
    (claimedUnique increasedCareCapacity careCapacityIsUndominated)

