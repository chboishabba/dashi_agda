module DASHI.Economics.AICapitalRoadmapMaxCut20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveNumericalCapitalBounds20261012Exact as Capital
import DASHI.Economics.AIOwnedSelfHostTCOEnvelope20261012Exact as TCO
import DASHI.Economics.AIMI355XAcquisitionDepreciationEnvelope20261014Exact as Quote
import DASHI.Economics.AICerebrasCloudMarginObserverBoundary20261012Exact as Margin
import DASHI.Economics.AICoreWeaveNamedPayerSaturation20261012Exact as Payer
import DASHI.Economics.AICoreWeaveAggregateCustomerCashRealisation20261014Exact as Cash
import DASHI.Economics.AICoreWeaveCapexDecompositionNonidentifiability20261012Exact as Replacement
import DASHI.Economics.AIAustraliaRegulatoryCostMeasurementBoundary20261014Exact as Regulation
import DASHI.Economics.AIPolicyReviewedCausalAttribution20261014Exact as Review
import DASHI.Economics.AIFinancingConditionsPanel20261014Exact as Financing
import DASHI.Economics.AIGalaxyHeliosLandlordEconomics20261014Exact as Landlord
import DASHI.Economics.AIInfrastructureStackReturnNonCollapse20261014Exact as Stack

------------------------------------------------------------------------
-- OCTOBER 14 TERMINAL MAX-CUT BOARD
------------------------------------------------------------------------

data CutState : Set where
  paid bounded partial empirical integration : CutState

record RoadmapLane : Set where
  constructor roadmap-lane
  field
    lane : String
    state : CutState
    paidSurface : String
    remainingSurface : String
    additionalGenericAbstractionScheduled : Bool

open RoadmapLane public

capitalReturnMagnitudeBounded : RoadmapLane
capitalReturnMagnitudeBounded = roadmap-lane
  "CoreWeave capital return"
  bounded
  "negative sign plus beta-free numerical WACC floor and capital-spread deficit lower bound under declared June-30 market-capital convention"
  "unique WACC/ROIC point only if a specific equity-risk model and canonical invested-capital convention are admitted"
  false

ownedNodeTCOPartial : RoadmapLane
ownedNodeTCOPartial = roadmap-lane
  "owned-vs-rented inference node TCO"
  partial
  "same-model rented-node price, eight-GPU bundled host-resource envelope, AMD reference power, benchmark electricity, current 8xMI355X commercial acquisition quote range and explicit five-/six-year depreciation coordinates"
  "resource-matched acquisition or lease terms, actual buyer financing/opportunity cost, facility PUE, labour, matched owner host/network/storage cost, residual value, maintenance and refresh risk"
  false

providerMarginalServingCostEmpirical : RoadmapLane
providerMarginalServingCostEmpirical = roadmap-lane
  "provider marginal inference economics"
  empirical
  "buyer-side same-model rented-node spread plus provider segment accounting margins and expected contract contribution-margin observations"
  "provider-owned realised marginal serving-cost ledger on matched model/configuration/SLA/cache/utilisation basis"
  false

terminalPayerGraphPartial : RoadmapLane
terminalPayerGraphPartial = roadmap-lane
  "terminal payer graph"
  partial
  "aggregate customer-cash collection is now source-paid; Microsoft and Meta external-cash-capacity edges, OpenAI contract/revenue-scale edge and CoreWeave contract-finance mechanism remain separately typed"
  "named-payer cash attribution, OpenAI external/operating cash provenance, realised named contract flows, anonymous current top-customer identities and residual financing/counterparty edges"
  false

replacementEconomicsEmpirical : RoadmapLane
replacementEconomicsEmpirical = roadmap-lane
  "replacement and economic-obsolescence burden"
  empirical
  "aggregate-capex non-identifiability theorem, accounting life and lender-horizon mismatch"
  "installed asset ages, acquisition vintages, actual retirements/refreshes, economic-life calibration, residual values and growth-vs-replacement capitalisation"
  false

regulatoryBurdenEmpirical : RoadmapLane
regulatoryBurdenEmpirical = roadmap-lane
  "AI regulatory burden and concentration causality"
  empirical
  "policy chronology, primary government business-impact survey instrument, typed causal-estimand/identification gate and exact SensibLaw human-review binding gate"
  "harmonised realised actor-class compliance costs, observed entry/open-weight/concentration response, comparator/control design, identification evidence and exact reviewed same-object causal bridge"
  false

financingConditionsHeterogeneous : RoadmapLane
financingConditionsHeterogeneous = roadmap-lane
  "AI infrastructure financing conditions"
  partial
  "Firmus failed IPO plus IMF/Goldman stress observations coexist with successful Tencent debt issuance"
  "harmonised issuer/project yield and credit-spread panel, refinancing outcomes, defaults/restructurings and realised investment returns"
  false

landlordLayerReturnPaid : RoadmapLane
landlordLayerReturnPaid = roadmap-lane
  "data-centre landlord/project economics"
  paid
  "Galaxy Helios Phase-II 13.7 percent starting gross yield-on-cost and 90-percent-plus lease-level NOI-margin target plus Q2 Phase-I recognised lease/operator revenue"
  "cash collection and Phase-II target realisation remain separate; this paid lane is not tenant/provider ROIC or terminal-demand authority"
  false

stackLayerNonCollapsePaid : RoadmapLane
stackLayerNonCollapsePaid = roadmap-lane
  "infrastructure-stack return non-collapse"
  paid
  "realised Galaxy landlord revenue and a bounded negative CoreWeave tenant capital spread coexist on the same stack"
  "terminal-customer economics and cash independence remain separate consumers"
  false

kernelReceiptIntegration : RoadmapLane
kernelReceiptIntegration = roadmap-lane
  "formal verification receipt"
  integration
  "source-written owners, RED-first/static regression surfaces, base-current branch topology and dedicated focused workflows"
  "successful exact-head Agda kernel/typecheck and runtime-suite receipts"
  false

additionalGenericAbstractionScheduledIsFalse :
  additionalGenericAbstractionScheduled capitalReturnMagnitudeBounded ≡ false
additionalGenericAbstractionScheduledIsFalse = refl

ownedTCOStillOpen : TCO.ownedTCOPaid TCO.mi355xOwnedEnvelope ≡ false
ownedTCOStillOpen = TCO.ownedTCOStillOpen

purchaseQuoteRangeNowPaid :
  Quote.purchaseQuoteRangeObserved Quote.mi355xAcquisitionDepreciationEnvelope ≡ true
purchaseQuoteRangeNowPaid = Quote.purchaseQuoteRangePaid

matchedRentalNodePurchasePriceStillOpen :
  Quote.matchedRentalNodePurchasePricePaid Quote.mi355xAcquisitionDepreciationEnvelope ≡ false
matchedRentalNodePurchasePriceStillOpen = Quote.matchedRentalNodePurchasePriceStillOpen

providerMarginalCostStillOpen :
  Margin.marginalInferenceServingMarginPaid Margin.cerebrasGaapCloudMargin ≡ false
providerMarginalCostStillOpen = Margin.marginalInferenceServingMarginStillOpen

aggregateCustomerCashNowPaid :
  Cash.aggregateCustomerCashReceiptPaid Cash.coreWeaveAggregateCustomerCash ≡ true
aggregateCustomerCashNowPaid = Cash.aggregateCustomerCashReceiptObserved

payerGraphStillNotExhaustive : Payer.exhaustiveTerminalGraphClosed Payer.coreWeavePayerSaturation ≡ false
payerGraphStillNotExhaustive = refl

regulatoryCostVectorStillOpen :
  Regulation.harmonisedRealisedCostVectorPaid Regulation.currentRegulatoryCostMeasurementStatus ≡ false
regulatoryCostVectorStillOpen = Regulation.harmonisedRealisedCostVectorPaidIsFalse

reviewedPolicyBridgeStillOpen :
  Review.reviewedSameObjectBridgePaid Review.currentAustralianReviewedPolicyStatus ≡ false
reviewedPolicyBridgeStillOpen = Review.reviewedSameObjectBridgeStillOpen

financingMarketNotUniversallyClosed :
  Financing.universalCapitalMarketClosure Financing.currentFinancingConditionsPanel ≡ false
financingMarketNotUniversallyClosed = refl

landlordRecognisedRevenuePaid :
  Landlord.realisedLeaseRevenuePaid Landlord.heliosPhaseIILandlordEconomics ≡ true
landlordRecognisedRevenuePaid = Landlord.realisedLeaseRevenueObserved

landlordCashCollectionStillOpen :
  Landlord.realisedLeaseCashCollectionPaid Landlord.heliosPhaseIILandlordEconomics ≡ false
landlordCashCollectionStillOpen = Landlord.cashCollectionStillOpen

stackLayerCoexistencePaid :
  (Landlord.realisedLeaseRevenuePaid Landlord.heliosPhaseIILandlordEconomics ≡ true) ×
  (Capital.capitalSpreadDeficitAtLeast578Bp ≡ true)
stackLayerCoexistencePaid = Stack.landlordRecognisedRevenueAndTenantNegativeSpreadCoexist

boundary : String
boundary =
  "The October-14 AI-capital programme is no longer missing a generic theory layer. CoreWeave aggregate customer-cash collection is source-paid while named-payer/terminal independence remains partial. Capital-return magnitude is bounded. Owned-node TCO is materially narrower: current 8xMI355X reseller quotes pay an acquisition-price/depreciation envelope, but resource-matched acquisition, financing, PUE, labour, residual and refresh economics remain partial. Provider marginal serving cost, replacement economics and realised regulatory-burden causality remain external empirical lanes. SensibLaw exact human review is now an explicit final gate after causal identification. Galaxy/Helios supplies contracted and recognised landlord coordinates while the same stack can simultaneously carry a negative CoreWeave tenant capital spread. Dedicated exact-head workflows now exist; successful kernel/runtime receipts remain the integration target."
