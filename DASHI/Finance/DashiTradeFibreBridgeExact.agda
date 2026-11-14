module DASHI.Finance.DashiTradeFibreBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Finance.TemporalMarketFibreExact as Temporal
import DASHI.Finance.PointInTimeUniverseFibreExact as PIT
import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb
import DASHI.Core.GovernanceTrajectoryRealisationExact as Governance
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as Viability

------------------------------------------------------------------------
-- Quant-finance / dashiTRADE bridge.
--
-- A learned residual policy proposes direction/weights inside a market fibre.
-- Existing dashiTRADE owners retain authority over actionability.  Signal,
-- authorization, execution and realized viability remain distinct stages.
------------------------------------------------------------------------

record TradeSituatedFibre : Set where
  constructor tradeSituatedFibre
  field
    marketFibre : Temporal.MarketFibre
    residualFibre : StatArb.ResidualFibre
    tradeFabric : Dream.TradingFabricState
    legacyWindow : Legacy.MarketWindowState
    bridgeReceipt : String

open TradeSituatedFibre public

record ProposalAdapter : Set where
  constructor proposalAdapter
  field
    learnedPolicy : StatArb.LearnedPolicy
    proposedDirection : Dream.Direction
    proposalReceipt : String
    proposalCreatesAuthorization : Bool
    proposalCreatesAuthorizationIsFalse : proposalCreatesAuthorization ≡ false

open ProposalAdapter public

------------------------------------------------------------------------
-- Permission remains owned by the existing dashiTRADE kernels.
------------------------------------------------------------------------

legacyPermissionFor : TradeSituatedFibre → Legacy.Permission
legacyPermissionFor state = Legacy.authorize (Legacy.quotient (legacyWindow state))

optionConeAvailable :
  TradeSituatedFibre → Dream.TradeAction → Set
optionConeAvailable state action =
  Dream.Available (tradeFabric state) action

holdAlwaysAvailableInFibre :
  (state : TradeSituatedFibre) →
  optionConeAvailable state Dream.holdAction
holdAlwaysAvailableInFibre state =
  Dream.holdAlwaysAvailable (tradeFabric state)

------------------------------------------------------------------------
-- Same learned proposal can inhabit distinct situated trade fibres and have
-- different realized actionability.  This reuses the exact dashiTRADE witness.
------------------------------------------------------------------------

data CanonicalBridgeTag : Set where
  canonicalBridge : CanonicalBridgeTag

canonicalMarket : Temporal.MarketFibre
canonicalMarket = Temporal.fibre0

canonicalResidual : StatArb.ResidualFibre
canonicalResidual =
  StatArb.residualFibre
    0
    StatArb.pca
    "canonical residual payload"
    "canonical PIT factor-fit receipt"
    (PIT.universeFibre
      0
      "historical constituents at t0"
      "historical membership receipt"
      true)
    "canonical residual provenance"

cleanLongTradeFibre : TradeSituatedFibre
cleanLongTradeFibre =
  tradeSituatedFibre
    canonicalMarket
    canonicalResidual
    Dream.cleanLongState
    (Legacy.marketState Legacy.upward Legacy.calm Legacy.persistent Legacy.adequate Legacy.clear 0 0 0 Legacy.HOLD)
    "clean long bridge"

crowdedLongTradeFibre : TradeSituatedFibre
crowdedLongTradeFibre =
  tradeSituatedFibre
    canonicalMarket
    canonicalResidual
    Dream.crowdedLongState
    (Legacy.marketState Legacy.upward Legacy.calm Legacy.persistent Legacy.adequate Legacy.clear 0 0 0 Legacy.HOLD)
    "crowded long bridge"

sameResidualAcrossTradeFibres :
  residualFibre cleanLongTradeFibre ≡ residualFibre crowdedLongTradeFibre
sameResidualAcrossTradeFibres = refl

sameLongDirectionAcrossTradeFibres :
  Dream.candidateObserver (tradeFabric cleanLongTradeFibre)
  ≡ Dream.candidateObserver (tradeFabric crowdedLongTradeFibre)
sameLongDirectionAcrossTradeFibres = Dream.sameLongProposal

buyAvailabilityDiffersAcrossTradeFibres :
  Dream.actionAvailable (tradeFabric cleanLongTradeFibre) Dream.buyAction
  ≡ Dream.actionAvailable (tradeFabric crowdedLongTradeFibre) Dream.buyAction →
  ⊥
buyAvailabilityDiffersAcrossTradeFibres = Dream.buyAvailabilityDiffers

------------------------------------------------------------------------
-- Therefore residual/proposal equality cannot be promoted to trade equality.
------------------------------------------------------------------------

record ResidualToTradeAuthorityBoundary : Set where
  constructor residualToTradeAuthorityBoundary
  field
    sameResidualImpliesSameActionability : Bool
    sameResidualImpliesSameActionabilityIsFalse :
      sameResidualImpliesSameActionability ≡ false
    sameDirectionImpliesAuthorization : Bool
    sameDirectionImpliesAuthorizationIsFalse :
      sameDirectionImpliesAuthorization ≡ false
    holdIsFirstClass : Bool
    holdIsFirstClassIsTrue : holdIsFirstClass ≡ true

canonicalResidualToTradeAuthorityBoundary : ResidualToTradeAuthorityBoundary
canonicalResidualToTradeAuthorityBoundary =
  residualToTradeAuthorityBoundary false refl false refl true refl

------------------------------------------------------------------------
-- Trajectory-cost bridge.
--
-- The stat-arb execution fibre records realized cost/impact provenance; the
-- existing dashiTRADE owner additionally treats execution, risk, turnover and
-- future optionality loss as trajectory coordinates.  We preserve that richer
-- decomposition rather than collapsing everything into one scalar slippage.
------------------------------------------------------------------------

record FinanceTradeTrajectory : Set where
  constructor financeTradeTrajectory
  field
    execution : StatArb.ExecutionFibre
    tradeRoute : Dream.TradeRoute
    trajectoryCost : Dream.TrajectoryCost
    routeCostMatchesDream : trajectoryCost ≡ Dream.costFor tradeRoute
    trajectoryReceipt : String

open FinanceTradeTrajectory public

lowTurnoverTrajectory : StatArb.ExecutionFibre → FinanceTradeTrajectory
lowTurnoverTrajectory execution =
  financeTradeTrajectory
    execution
    Dream.lowTurnoverRoute
    (Dream.costFor Dream.lowTurnoverRoute)
    refl
    "finance execution mapped to dashiTRADE low-turnover trajectory"

churnTrajectory : StatArb.ExecutionFibre → FinanceTradeTrajectory
churnTrajectory execution =
  financeTradeTrajectory
    execution
    Dream.churnRoute
    (Dream.costFor Dream.churnRoute)
    refl
    "finance execution mapped to dashiTRADE churn trajectory"

sameEndpointDoesNotEraseTrajectoryCost :
  Dream.totalCost (trajectoryCost (lowTurnoverTrajectory
    (StatArb.executionFibre 1 "same fill" "cost" "impact" "receipt")))
  ≡
  Dream.totalCost (trajectoryCost (churnTrajectory
    (StatArb.executionFibre 1 "same fill" "cost" "impact" "receipt"))) →
  ⊥
sameEndpointDoesNotEraseTrajectoryCost =
  Dream.sameEndpointDifferentTrajectoryCost

------------------------------------------------------------------------
-- GJR-GARCH volatility observer.
--
-- Glosten, Jagannathan and Runkle (1993) own the asymmetric conditional
-- variance model.  DASHI owns this finite source-bounded adapter.
--
-- Values use the article's displayed integer scales:
--   restingVolTenthsPercent : annualized percent x 10
--   alpha/beta/gamma        : coefficient x 1000
--
-- The observer is evidence.  It cannot authorize a trade.
------------------------------------------------------------------------

record GJRVolatilityObservation : Set where
  constructor gjrVolatilityObservation
  field
    restingVolTenthsPercent : Nat
    alphaThousandths : Nat
    betaThousandths : Nat
    gammaThousandths : Nat
    halfDecayTradingDays : Nat
    sourceReceipt : String
    observationCreatesAuthorization : Bool
    observationCreatesAuthorizationIsFalse :
      observationCreatesAuthorization ≡ false

open GJRVolatilityObservation public

positiveShockKick : GJRVolatilityObservation → Nat
positiveShockKick observation = alphaThousandths observation

downsideShockKick : GJRVolatilityObservation → Nat
downsideShockKick observation =
  alphaThousandths observation + gammaThousandths observation

twiceExpectedPersistence : GJRVolatilityObservation → Nat
twiceExpectedPersistence observation =
  alphaThousandths observation
  + alphaThousandths observation
  + betaThousandths observation
  + betaThousandths observation
  + gammaThousandths observation

historicalGJR1985To2000 : GJRVolatilityObservation
historicalGJR1985To2000 =
  gjrVolatilityObservation
    154 31 936 44 65
    "Michael Burry, Cassandra Unchained, 2026-08-01 chart; GJR attribution retained"
    false refl

modernGJR2011To2026 : GJRVolatilityObservation
modernGJR2011To2026 =
  gjrVolatilityObservation
    167 0 833 282 27
    "Michael Burry, Cassandra Unchained, 2026-08-01 chart; GJR attribution retained"
    false refl

historicalPositiveKickIs31 :
  positiveShockKick historicalGJR1985To2000 ≡ 31
historicalPositiveKickIs31 = refl

historicalDownsideKickIs75 :
  downsideShockKick historicalGJR1985To2000 ≡ 75
historicalDownsideKickIs75 = refl

modernPositiveKickIsZero :
  positiveShockKick modernGJR2011To2026 ≡ 0
modernPositiveKickIsZero = refl

modernDownsideKickIs282 :
  downsideShockKick modernGJR2011To2026 ≡ 282
modernDownsideKickIs282 = refl

historicalTwiceExpectedPersistenceIs1978 :
  twiceExpectedPersistence historicalGJR1985To2000 ≡ 1978
historicalTwiceExpectedPersistenceIs1978 = refl

modernTwiceExpectedPersistenceIs1948 :
  twiceExpectedPersistence modernGJR2011To2026 ≡ 1948
modernTwiceExpectedPersistenceIs1948 = refl

historicalHalfDecayIs65 :
  halfDecayTradingDays historicalGJR1985To2000 ≡ 65
historicalHalfDecayIs65 = refl

modernHalfDecayIs27 :
  halfDecayTradingDays modernGJR2011To2026 ≡ 27
modernHalfDecayIs27 = refl

------------------------------------------------------------------------
-- Classification remains separate from authorization.
------------------------------------------------------------------------

record GJRLegacyClassification : Set where
  constructor gjrLegacyClassification
  field
    observation : GJRVolatilityObservation
    energyClass : Legacy.EnergyInvariant
    persistenceClass : Legacy.PersistenceInvariant
    classificationReceipt : String
    classificationCreatesAuthorization : Bool
    classificationCreatesAuthorizationIsFalse :
      classificationCreatesAuthorization ≡ false

open GJRLegacyClassification public

historicalGJRClassification : GJRLegacyClassification
historicalGJRClassification =
  gjrLegacyClassification
    historicalGJR1985To2000
    Legacy.ordinary
    Legacy.persistent
    "displayed GJR coefficients classified for the legacy market-window observer"
    false refl

modernGJRClassification : GJRLegacyClassification
modernGJRClassification =
  gjrLegacyClassification
    modernGJR2011To2026
    Legacy.stressed
    Legacy.transient
    "larger downside kick and shorter displayed half-decay remain separate coordinates"
    false refl

------------------------------------------------------------------------
-- Equal resting volatility does not determine shock dynamics.
--
-- This is a structural witness.  It is not an empirical claim that the two
-- Burry eras have equal resting volatility.
------------------------------------------------------------------------

sameRestingSlowMemory : GJRVolatilityObservation
sameRestingSlowMemory =
  gjrVolatilityObservation
    160 30 935 45 65
    "structural non-factorability witness"
    false refl

sameRestingFastMemory : GJRVolatilityObservation
sameRestingFastMemory =
  gjrVolatilityObservation
    160 0 830 280 27
    "structural non-factorability witness"
    false refl

sameRestingVolatility :
  restingVolTenthsPercent sameRestingSlowMemory
  ≡ restingVolTenthsPercent sameRestingFastMemory
sameRestingVolatility = refl

sameRestingDifferentDownsideKick :
  downsideShockKick sameRestingSlowMemory
  ≡ downsideShockKick sameRestingFastMemory →
  ⊥
sameRestingDifferentDownsideKick ()

------------------------------------------------------------------------
-- O / R / C / S / L / P / G / F governance view.
--
-- This instantiates the existing governance owner.  The governance gate admits
-- observation and classification.  It does not grant trade authority.
------------------------------------------------------------------------

data TradeGovernanceOrganization : Set where
  dashiTrade : TradeGovernanceOrganization

data TradeGovernanceRequirement : Set where
  pointInTimeVolatilityEvidence : TradeGovernanceRequirement
  separateTradeAuthorization : TradeGovernanceRequirement

data TradeGovernanceCode : Set where
  gjrObserverCode : TradeGovernanceCode
  optionConeCode : TradeGovernanceCode

data TradeGovernanceState : Set where
  historicalEra : TradeGovernanceState
  modernEra : TradeGovernanceState

data TradeGovernanceLattice : Set where
  observedEvidence : TradeGovernanceLattice
  classifiedEvidence : TradeGovernanceLattice

data TradeGovernanceProposal : Set where
  observeVolatility : TradeGovernanceProposal
  classifyVolatility : TradeGovernanceProposal
  authorizeTrade : TradeGovernanceProposal

data TradeGovernanceGap : Set where
  evidenceGapClosed : TradeGovernanceGap
  authorizationGapOpen : TradeGovernanceGap

tradeGovernanceGate :
  TradeGovernanceProposal → TradeGovernanceState → Bool
tradeGovernanceGate observeVolatility state = true
tradeGovernanceGate classifyVolatility state = true
tradeGovernanceGate authorizeTrade state = false

tradeGovernanceGap :
  TradeGovernanceOrganization →
  TradeGovernanceRequirement →
  TradeGovernanceCode →
  TradeGovernanceState →
  TradeGovernanceLattice →
  TradeGovernanceGap
tradeGovernanceGap organization pointInTimeVolatilityEvidence code state lattice =
  evidenceGapClosed
tradeGovernanceGap organization separateTradeAuthorization code state lattice =
  authorizationGapOpen

canonicalGJRTradeGovernance :
  Governance.ZKPGovernanceModel
    TradeGovernanceOrganization
    TradeGovernanceRequirement
    TradeGovernanceCode
    TradeGovernanceState
    TradeGovernanceLattice
    TradeGovernanceProposal
    TradeGovernanceGap
canonicalGJRTradeGovernance =
  Governance.zkp-governance-model
    dashiTrade
    pointInTimeVolatilityEvidence
    gjrObserverCode
    modernEra
    classifiedEvidence
    classifyVolatility
    tradeGovernanceGate
    tradeGovernanceGap

gjrGovernanceBlocksDirectTradeAuthority :
  Governance.G canonicalGJRTradeGovernance authorizeTrade modernEra ≡ false
gjrGovernanceBlocksDirectTradeAuthority = refl

record GJRTradeContract : Set where
  constructor gjrTradeContract
  field
    preconditionSourceReceiptPresent : Bool
    preconditionScaleDeclared : Bool
    invariantShockAndPersistenceSeparate : Bool
    invariantObservationDoesNotAuthorize : Bool
    postconditionClassificationAvailable : Bool
    postconditionPermissionRemainsExternal : Bool

open GJRTradeContract public

canonicalGJRTradeContract : GJRTradeContract
canonicalGJRTradeContract =
  gjrTradeContract true true true true true true

------------------------------------------------------------------------
-- Declared/realized viability cross-pollination is preserved as a residual.
------------------------------------------------------------------------

cleanLongViabilityAligned :
  Viability.viabilityResidual
    Dream.longDirection
    (Dream.actionAvailable Dream.cleanLongState Dream.buyAction)
  ≡ Viability.proposalViabilityAligned
cleanLongViabilityAligned = refl

crowdedLongViabilityMismatch :
  Viability.viabilityResidual
    Dream.longDirection
    (Dream.actionAvailable Dream.crowdedLongState Dream.buyAction)
  ≡ Viability.proposalViabilityMismatch
crowdedLongViabilityMismatch = refl

bridgeBoundaryStatement : String
bridgeBoundaryStatement =
  "A factor-residual or learned-policy proposal is only a candidate direction inside a temporal market fibre. dashiTRADE permission, situated option-cone actionability, trajectory cost, and declared/realized viability remain independent proof-bearing stages before execution authority."
