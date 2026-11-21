module DASHI.Economics.MacroFinancialTemporalConsumer20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Economics.JPYJGBTreasuryFundingTransmission2026Exact as Yen
import DASHI.Economics.AIGlobalFundingRegulatorySynthesisExact as Global
import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Capital
import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Outcome
import DASHI.Economics.ChinaRetailGoldMarketTopology2026Exact as Gold
import DASHI.Economics.AICapitalBurdenRelocation20261012Exact as Burden
import DASHI.Economics.JPYTreasuryOpposingFlow20261121Exact as Treasury
import DASHI.Economics.JPYTreasuryInterventionOfficialReceipts20261121Exact as FX
import DASHI.Economics.TreasuryParYieldEventWindow20261121Exact as CMT
import DASHI.Economics.TreasuryAuctionJapanFlow20261121Exact as AuctionFlow
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

-- Relative clock ticks on a common declared timeline, not calendar parsing.
-- A historical event can be disclosed later; a plan is not settlement.
data AtMost : Nat → Nat → Set where
  zeroAtMost : ∀ {n} → AtMost zero n
  stepAtMost : ∀ {m n} → AtMost m n → AtMost (suc m) (suc n)

data SettlementClock : Set where
  settlementUnknown : SettlementClock
  settlementAt : Nat → SettlementClock

record TemporalAttachment (asOf : Nat) : Set where
  constructor temporalAttachment
  field
    scope : String
    actor : String
    sourceId : String
    eventTick : Nat
    disclosureTick : Nat
    actorKnowledgeTick : Nat
    eventBeforeCut : AtMost eventTick asOf
    disclosureBeforeCut : AtMost disclosureTick asOf
    knowledgeBeforeCut : AtMost actorKnowledgeTick asOf
    settlement : SettlementClock

open TemporalAttachment public

-- Settlement admission is a separate typed witness, never inferred from disclosure.
record SettledBy {asOf : Nat} (a : TemporalAttachment asOf) : Set where
  field
    tick : Nat
    settlementMatches : settlement a ≡ settlementAt tick
    settlementBeforeCut : AtMost tick asOf

record ExistingStateAttachment (asOf : Nat) : Set where
  field
    timeline : TemporalAttachment asOf
    coupledState : Global.CoupledState
    capitalPoint : Capital.ObservedCapitalStatePoint
    goldBoundary : Gold.ChinaRetailGoldTopologyBoundary
    burdenState : Burden.CapitalBurdenState
    treasuryFlow : Treasury.TreasuryOpposingPressure

-- The intent coordinate is deliberately a synthetic rival-world discriminator.
-- Identical observed economics can coexist with distinct intended objectives.
data CorrectionObjective : Set where
  endogenousCorrection deliberateTolerance deliberateInduction
  selectiveCorporateIntervention disorderlyContagion : CorrectionObjective

record RivalWorld (asOf : Nat) : Set where
  constructor rivalWorld
  field
    observed : ExistingStateAttachment asOf
    objective : CorrectionObjective

open RivalWorld public

sameObservationDifferentObjective :
  ∀ {t} (s : ExistingStateAttachment t) →
  Descent.ConsumerNonDescentWitness
    (observed {asOf = t}) (objective {asOf = t})
sameObservationDifferentObjective s =
  Descent.consumerNonDescentWitness
    (rivalWorld s endogenousCorrection)
    (rivalWorld s deliberateInduction)
    refl (λ ())

observationDoesNotDetermineIntent :
  ∀ {t} (s : ExistingStateAttachment t) →
  Descent.FactorsThrough
    (observed {asOf = t}) (objective {asOf = t}) → ⊥
observationDoesNotDetermineIntent s =
  Descent.nonDescentWitnessBlocksFactorization
    (sameObservationDifferentObjective s)

-- Five testable scenario labels need not be mutually exclusive in reality.
-- Here each is a synthetic observer-consumer label: neither an empirical
-- classification nor proof of public-actor motive.

data ScenarioIndex : Set where
  H0 H1 H2 H3 H4 : ScenarioIndex

scenarioObjective : ScenarioIndex → CorrectionObjective
scenarioObjective H0 = endogenousCorrection
scenarioObjective H1 = deliberateTolerance
scenarioObjective H2 = deliberateInduction
scenarioObjective H3 = selectiveCorporateIntervention
scenarioObjective H4 = disorderlyContagion

-- Signed evidence and observables cannot be replaced with a statement of intent.
-- Separate documentary scope/join admission from a common chart projection.
record SameObjectJoin (asOf : Nat) : Set where
  field
    state : ExistingStateAttachment asOf
    scopeAndSourceCompared : Bool
    scopeAndSourceComparedIsTrue : scopeAndSourceCompared ≡ true
    timeUnitsCompared : Bool
    timeUnitsComparedIsTrue : timeUnitsCompared ≡ true
    marketQuoteAsOfCompared : Bool
    marketQuoteAsOfComparedIsTrue : marketQuoteAsOfCompared ≡ true

-- This proves only that all *declared* gate flags hold, not that any real
-- observations satisfy them. Evidence must be supplied at the input boundary.
-- The economic value and the policy-intent consumer remain distinct.
joinRetainsObservation : ∀ {t} (j : SameObjectJoin t) → ExistingStateAttachment t
joinRetainsObservation = SameObjectJoin.state

-- Existing alternative-regime fits are retained, not assigned to new actors.
existingRefinancingFit : Outcome.OutcomeFit
existingRefinancingFit = Outcome.refinancingStressFit

existingYenBridge : Yen.CrossMarketFundingBridge
existingYenBridge = Yen.candidateCrossMarketBridge

-- Public dashiTRADE adapter counterpart: signals/treasury_opposing_flow_20261121.py
-- These structural calculations share the exact synthetic 8/2/3/2/1 and
-- 1/1/3/2/1 vectors. Do not interpret these as calibrated financial values.
-- Source, window, units, and market-as-of authority remain independent gates.
syntheticLowerPressure : Treasury.downward Treasury.flightFixture ≡ 10
syntheticLowerPressure = refl

syntheticHigherPressure : Treasury.upward Treasury.repatriationFixture ≡ 6
syntheticHigherPressure = refl

syntheticRepatriationDownward : Treasury.downward Treasury.repatriationFixture ≡ 2
syntheticRepatriationDownward = refl

sameJPYOppositeYieldDirection :
  (Treasury.outcome Treasury.flightLower ≡ Treasury.lowerYield) ×
  (Treasury.outcome Treasury.repatriationHigher ≡ Treasury.higherYield)
sameJPYOppositeYieldDirection = Treasury.oppositeOutcomeDespiteSameJPY

-- Real operation receipts remain distinct from the wholly synthetic channel
-- elasticity/pressure fixtures and from the USD-denominated photographed plan.
originalJapanQuarterTotal : FX.japanQuarterTotal ≡ 153993
originalJapanQuarterTotal = FX.japanTotalMatchesOfficial

originalUSSpotYen : FX.yenBoughtTenthsBillion FX.usJuly31 ≡ 794
originalUSSpotYen = refl

-- Original fixed-maturity CMT rates (historical research observations) are
-- independent of the actor's contemporaneous information and the auction
-- actual stop-out yield. No intervention response is causally isolated.
actualWindowTenYearThreeBpHigher :
  CMT.tenYearBasisPoints CMT.july29 + 3 ≡
  CMT.tenYearBasisPoints CMT.august03
actualWindowTenYearThreeBpHigher = CMT.windowTenYearThreeBpHigher

actualWindowThirtyYearThreeBpHigher :
  CMT.thirtyYearBasisPoints CMT.july29 + 3 ≡
  CMT.thirtyYearBasisPoints CMT.august03
actualWindowThirtyYearThreeBpHigher = CMT.windowThirtyYearThreeBpHigher

-- A primary Treasury 10-year auction and a secondary aggregate Japanese
-- portfolio-flow series are observed, but share no paid security, investor,
-- custody or execution-window join. Prevent original evidence laundering.
tenYearAuctionYield :
  AuctionFlow.highYieldThousandthPercent AuctionFlow.tenYearNovember ≡ 5020
tenYearAuctionYield = AuctionFlow.tenYearHighYieldExact

japanJulyNetPurchasesExact :
  AuctionFlow.purchasesTenthsBillionJPY AuctionFlow.julyResidentForeignDebt ≡
  AuctionFlow.salesTenthsBillionJPY AuctionFlow.julyResidentForeignDebt + 3657
japanJulyNetPurchasesExact = AuctionFlow.julyNetExact

japanAugustRoundingExact :
  AuctionFlow.reportedNetMagnitudeTenthsBillionJPY AuctionFlow.augustResidentForeignDebt + 1 ≡ 1431
japanAugustRoundingExact = AuctionFlow.augustReportedRoundingDifference
