module DASHI.Economics.AICapitalRoadmapMaxCut20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveNumericalCapitalBounds20261012Exact as Capital
import DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact as Rental
import DASHI.Economics.AIOwnedSelfHostTCOEnvelope20261012Exact as TCO
import DASHI.Economics.AICoreWeaveContributionMarginExpectation20261012Exact as CoreMargin
import DASHI.Economics.AICerebrasCloudMarginObserverBoundary20261012Exact as CerebrasMargin
import DASHI.Economics.AIEqualIndexOpenClosedSpread20261012Exact as EqualIndex
import DASHI.Economics.AIOpenAIPayerRevenueCapacity20261012Exact as OpenAIPayer
import DASHI.Economics.AICoreWeaveCapexDecompositionNonidentifiability20261012Exact as Capex
import DASHI.Economics.AIAccountingFinancingLifeGap20261012Exact as LifeGap
import DASHI.Economics.AIAustraliaPostHearingPolicy20261012Exact as PostHearing
import DASHI.Economics.AIPolicyCausalEstimandIdentification20261012Exact as PolicyID
import DASHI.Economics.AIFirmusMarketAccessStress20261012Exact as Firmus

------------------------------------------------------------------------
-- FINAL MAX-CUT ROADMAP
--
-- The point of this owner is a stopping rule.  A lane is not kept "open" just
-- because its strongest imaginable quantity is absent: it records what has
-- actually been paid, what is bounded/partial, and whether further progress is
-- now an empirical acquisition or repository-integration obligation rather
-- than another abstract theorem.
------------------------------------------------------------------------

data RoadmapState : Set where
  paid bounded partial empirical integration : RoadmapState

record RoadmapLane : Set where
  constructor roadmap-lane
  field
    lane : String
    state : RoadmapState
    paidSurface : String
    remainingProducer : String
    anotherAbstractLayerScheduled : Bool

open RoadmapLane public

numericalCapitalReturnBounded : RoadmapLane
numericalCapitalReturnBounded = roadmap-lane
  "CoreWeave numerical ROIC-WACC"
  bounded
  "declared June-30 market-capital ROIC magnitude 45-46bp negative; beta-free WACC floor >533bp; capital-spread deficit >578bp"
  "a unique WACC point requires an admitted equity-risk model/beta/ERP; canonical ROIC convention remains a modelling choice"
  false

ownedSelfHostTCOBounded : RoadmapLane
ownedSelfHostTCOBounded = roadmap-lane
  "owned self-host TCO"
  bounded
  "selected rented-GPU comparator corrected; MI355X rental break-even USD 22,688.40/GPU-year with benchmark electricity about USD 1,405.76/GPU-year"
  "purchase price/depreciation or lease terms, financing/opportunity cost, facility PUE, labour, host/network/storage, residual value and refresh risk"
  false

providerMarginalInferenceCostStillOpen : RoadmapLane
providerMarginalInferenceCostStillOpen = roadmap-lane
  "provider marginal inference economics"
  empirical
  "same-model rented-GPU cost; buyer-side crack spread; Cerebras segment accounting margin; CoreWeave signed-contract expected contribution-margin improvement"
  "provider-owned realised marginal serving-cost ledger under a matched model/configuration/SLA/cache/utilisation basis"
  false

equalAggregateIndexSpreadPaid : RoadmapLane
equalAggregateIndexSpreadPaid = roadmap-lane
  "open-vs-closed matched scalar performance spread"
  paid
  "MiMo-V2.6-Pro and GPT-6 Astra Low both score Intelligence Index 46 while closed cost/task is >6x and blended token price >43x"
  "none for the equal-aggregate-index claim"
  false

fullCapabilityMatchedScarcityRentStillOpen : RoadmapLane
fullCapabilityMatchedScarcityRentStillOpen = roadmap-lane
  "full-capability matched scarcity rent"
  empirical
  "aggregate-index collision is paid and component-vector differences are explicit"
  "a declared equivalence class over task mix, component capability vector, tool access, context, latency/SLA and accounting denominator"
  false

openAIPayerCapacityPartial : RoadmapLane
openAIPayerCapacityPartial = roadmap-lane
  "terminal payer saturation"
  partial
  "Microsoft and Meta external-cash-capacity edges; OpenAI CoreWeave contract plus approximately USD 50B annualised revenue-scale evidence"
  "OpenAI operating/external-customer cash provenance, realised CoreWeave contract payments, anonymous current top-customer identities and residual counterparty loops"
  false

replacementEconomicsPartial : RoadmapLane
replacementEconomicsPartial = roadmap-lane
  "replacement / obsolescence economics"
  partial
  "aggregate capex non-identifiability proved; CoreWeave 72-month accounting life; generic lender GPU horizon 36-48 months; 24-36 month life-gap pressure coordinate"
  "installed asset-age distribution, actual retirements/refreshes, economic-life calibration and growth-vs-replacement capitalisation"
  false

postHearingPolicyChronologyPaid : RoadmapLane
postHearingPolicyChronologyPaid = roadmap-lane
  "Australian post-hearing policy chronology"
  paid
  "Medicare incident -> OpenAI apology/monitoring response and serious-incident-reporting proposal; earlier mandatory-guardrail proposal not proceeding at this time"
  "none for chronology/outcome observation"
  false

policyMarketCausalIdentificationStillOpen : RoadmapLane
policyMarketCausalIdentificationStillOpen = roadmap-lane
  "regulatory burden -> entry/open-weight/concentration causal effect"
  empirical
  "typed causal-estimand and identification-family gate already exist"
  "realised same-basis compliance-cost microdata, market response, comparator/control strategy and reviewed identification receipt; intentional capture remains separate"
  false

firmusMarketAccessStressPaid : RoadmapLane
firmusMarketAccessStressPaid = roadmap-lane
  "AI-infrastructure capital-market access stress"
  paid
  "Firmus planned USD 5B IPO at implied USD 30.6B valuation withdrawn amid reported debt/execution/valuation concerns"
  "broader harmonised issuance/yield/default/refinancing panel before sector-wide promotion"
  false

integrationReceiptStillOpen : RoadmapLane
integrationReceiptStillOpen = roadmap-lane
  "repository integration and verification"
  integration
  "source owners and static/executable regression sources written"
  "restack against current master/main as needed plus exact-head Agda/kernel and Python/runtime receipts"
  false

------------------------------------------------------------------------
-- Cross-owner receipts that pin the stronger stopping state.
------------------------------------------------------------------------

capitalWACCFloorPaid : Capital.betaFreeWACCFloorPaid ≡ true
capitalWACCFloorPaid = refl

rentalIsNotOwnedTCO : Rental.ownedHardwareTCO Rental.miniMaxM3EngineeringComparison ≡ false
rentalIsNotOwnedTCO = Rental.ownedHardwareTCOPaidIsFalse

ownedTCOStillNeedsAcquisition : TCO.ownedTCOPaid TCO.mi355xOwnedEnvelope ≡ false
ownedTCOStillNeedsAcquisition = TCO.ownedTCOStillOpen

coreWeaveExpectedMarginNotRealised :
  CoreMargin.realisedContributionMarginPaid CoreMargin.coreWeaveQ2SignedContractExpectation ≡ false
coreWeaveExpectedMarginNotRealised = CoreMargin.realisedContributionMarginPaidIsFalse

cerebrasMarginalInferenceStillOpen :
  CerebrasMargin.marginalInferenceServingMarginPaid CerebrasMargin.cerebrasGaapCloudMargin ≡ false
cerebrasMarginalInferenceStillOpen = CerebrasMargin.marginalInferenceServingMarginStillOpen

equalIndexScalarPaid : EqualIndex.sameAggregateIndexPaid EqualIndex.mimoAstraEqualIndexPair ≡ true
equalIndexScalarPaid = EqualIndex.sameAggregateIndexPaidReceipt

equalIndexVectorStillOpen : EqualIndex.sameCapabilityVectorPaid EqualIndex.mimoAstraEqualIndexPair ≡ false
equalIndexVectorStillOpen = EqualIndex.sameCapabilityVectorPaidIsFalse

openAIRevenueCapacityPaid : OpenAIPayer.revenueScaleCapacityPaid OpenAIPayer.openAICoreWeaveCapacity ≡ true
openAIRevenueCapacityPaid = OpenAIPayer.revenueScaleCapacityObserved

openAICashProvenanceStillOpen : OpenAIPayer.externalCustomerCashProvenancePaid OpenAIPayer.openAICoreWeaveCapacity ≡ false
openAICashProvenanceStillOpen = OpenAIPayer.externalCustomerCashProvenancePaidIsFalse

replacementAggregateStillNonidentifying : Capex.aggregateCapexCollisionPaid ≡ true
replacementAggregateStillNonidentifying = refl

lifeGapPressurePaid : LifeGap.lifeGapIsObsolescencePressureEvidence LifeGap.coreWeaveAccountingVsLenderGPUHorizon ≡ true
lifeGapPressurePaid = LifeGap.obsolescencePressureCoordinatePaid

postHearingChronologyPaid : PostHearing.incidentResponseChronologyPaidField PostHearing.currentPostHearingPolicyState ≡ true
postHearingChronologyPaid = PostHearing.incidentResponseChronologyPaid

policyIdentificationStillUnpaid : PolicyID.currentPolicyIdentificationPaid PolicyID.currentAustralianPolicyCausalStatus ≡ false
policyIdentificationStillUnpaid = PolicyID.currentPolicyIdentificationStillOpen

firmusStressObserved : Firmus.investorSelectivityStress Firmus.firmusOctober2026Stress ≡ true
firmusStressObserved = Firmus.investorSelectivityStressObserved

remainingFrontierIsEmpiricalOrIntegration : Bool
remainingFrontierIsEmpiricalOrIntegration = true

boundary : String
boundary =
  "After the October-12 max-cut, the major remaining AI-capital questions no longer need another generic formal layer. Numerical CoreWeave capital return is bounded rather than merely sign-known; the rented-GPU comparator has been corrected and an owned-TCO break-even envelope paid; an exact equal-aggregate-index open/closed price spread is paid while full capability-vector equivalence remains open; OpenAI payer capacity is narrowed by revenue-scale evidence without cash-provenance promotion; replacement economics has exact non-identifiability and life-gap bounds; the Australian post-hearing incident/policy chronology is paid while causal concentration/capture identification remains empirical; Firmus supplies a realised market-access stress event. The residual frontier is source acquisition, matched empirical identification, or exact-head repository integration/verification."
