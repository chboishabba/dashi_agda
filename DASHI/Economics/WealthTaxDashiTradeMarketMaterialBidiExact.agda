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
open import Agda.Builtin.Nat using (Nat)
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
