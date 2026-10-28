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
open import Data.Nat.Properties using (m≤m+n; ≤-trans; +-assoc; +-comm; m+n∸n≡m)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
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

-- The net batch is a participant-level financial observation. The
-- original two-fill sale is an investor-level synthetic fixture. No implicit
-- identification of the two records is supplied by this code.


------------------------------------------------------------------------
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
