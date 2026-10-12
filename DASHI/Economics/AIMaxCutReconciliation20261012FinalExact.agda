module DASHI.Economics.AIMaxCutReconciliation20261012FinalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIMaxCutReconciliation20261012Exact as Prior
import DASHI.Economics.AIFixedBasketMarketSeries20261012Exact as Basket
import DASHI.Economics.AIOpenWeightTrajectory20261012Exact as OpenTrajectory
import DASHI.Economics.AIQualityNormalizedPriceSpread20261012Exact as QualityPrice
import DASHI.Economics.AITwoSidedConcentrationPropagation20261012Exact as Concentration
import DASHI.Economics.AICoreWeaveDebtCostBoundary20261012Exact as DebtCost
import DASHI.Economics.AICoreWeaveCapitalSpreadSign20261012Exact as CapitalSign
import DASHI.Economics.AICoreWeaveCapitalReinvestmentCoverage20261012Exact as Reinvestment
import DASHI.Economics.AICoreWeaveCapexDecompositionNonidentifiability20261012Exact as CapexDecomposition
import DASHI.Economics.AICoreWeaveAssetLifeObsolescenceBoundary20261012Exact as AssetLife
import DASHI.Economics.AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact as TerminalPayer
import DASHI.Economics.AICoreWeaveNamedPayerSaturation20261012Exact as PayerSaturation
import DASHI.Economics.AITerminalPayerConsumerSufficiency20261012Exact as PayerConsumer
import DASHI.Economics.AICapitalObserverNonDescent20261012Exact as CapitalObserver
import DASHI.Economics.AIPolicyCausalAdmission20261012Exact as PolicyCausal
import DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact as SelfHostCost

------------------------------------------------------------------------
-- FINAL OCTOBER-12 RECONCILIATION
------------------------------------------------------------------------

data FinalState : Set where
  open partial paid : FinalState

record FinalProducer : Set where
  constructor finalProducer
  field
    producer : String
    state : FinalState
    scope : String
    receipt : String
    promotesGlobalCapitalRecovery : Bool

open FinalProducer public

selectedPublicEquityDynamicsPaid : FinalProducer
selectedPublicEquityDynamicsPaid = finalProducer
  "fixed-composition public-equity flip/volatility" paid
  "equal-weight CRWV/ORCL/AVGO; seven sessions 2026-10-01..2026-10-09"
  "4 flips over 6 transitions; 66.67 percent flip rate; 2.8644 percent population daily realised volatility" false

vercelOpenWeightTrajectoryPaid : FinalProducer
vercelOpenWeightTrajectoryPaid = finalProducer
  "same-platform open-weight token-share trajectory" paid "Vercel AI Gateway"
  "open-weight token share rises from 56.0 percent in August to 61.3 percent on 2026-10-10, +5.3 percentage points" false

selectedBenchmarkPricePairPaid : FinalProducer
selectedBenchmarkPricePairPaid = finalProducer
  "selected benchmark-normalised open/closed API-price pair" paid
  "Artificial Analysis Intelligence Index: MiMo-V2.6-Pro vs Claude Opus 5.5 Max"
  "reported cost per index task and score imply approximately 36.483x closed/open cost-per-index-point ratio for this selected pair" false

sameModelSelfHostEngineeringCostPaid : FinalProducer
sameModelSelfHostEngineeringCostPaid = finalProducer
  "same-model hosted-vs-self-host engineering cost comparator" paid
  "MiniMax-M3; AMD MI355X; concurrency 512; 1k input; 30 percent sustained utilisation"
  "public engineering dataset estimates USD 0.93/M output tokens self-hosted versus USD 1.20/M hosted for the same model under the declared configuration; source conflict and configuration sensitivity are retained" false

headlineObserverNonDescentPaid : FinalProducer
headlineObserverNonDescentPaid = finalProducer
  "headline-observer non-descent for capital recovery" paid "synthetic logical countermodel"
  "identical revenue/usage/valuation/market-price headline surfaces can hide different terminal-payer or capital-spread coordinates and therefore different recovery outcomes; every sufficient refinement must separate the witnessed collision" false

coreWeaveTwoSidedConcentrationPaid : FinalProducer
coreWeaveTwoSidedConcentrationPaid = finalProducer
  "CoreWeave two-sided concentration topology" paid
  "CoreWeave Q2-2026 customer side + Core Scientific H1-2026 provider side"
  "CoreWeave top-three customers account for 72 percent with HHI bounds 0.2072..0.2856; CoreWeave is approximately 77 percent of Core Scientific H1 revenue" false

coreWeaveDebtCostSurfacePaid : FinalProducer
coreWeaveDebtCostSurfacePaid = finalProducer
  "CoreWeave debt-cost surface" paid "CoreWeave H1/Q2-2026"
  "H1 contractual debt interest USD 1.075B, reported total debt interest USD 0.985B, future principal USD 35.551B; selected non-convertible effective/stated rates span 8.5 to 15 percent" false

coreWeaveCapitalSpreadSignPaid : FinalProducer
coreWeaveCapitalSpreadSignPaid = finalProducer
  "CoreWeave ROIC-WACC sign under declared standard sign conditions" paid
  "CoreWeave H1-2026 / sign-only capital-return model"
  "source-paid operating loss plus positive debt principal/rates imply negative ROIC and positive WACC under declared positive-invested-capital/debt-contribution and non-negative-equity-contribution conditions" false

coreWeaveReinvestmentCoveragePaid : FinalProducer
coreWeaveReinvestmentCoveragePaid = finalProducer
  "CoreWeave same-period internal reinvestment coverage" paid "CoreWeave H1-2026"
  "operating cash flow USD 3.663B versus capex USD 14.117B leaves an exact USD 10.454B same-period internal-cash shortfall" false

coreWeaveCapexNonidentifiabilityPaid : FinalProducer
coreWeaveCapexNonidentifiabilityPaid = finalProducer
  "aggregate-capex decomposition non-identifiability" paid "CoreWeave H1-2026 / generic accounting decomposition"
  "two valid growth/maintenance/replacement decompositions have identical USD 14.117B aggregate capex but different replacement amounts; no function of aggregate capex alone can recover replacement capex for every valid decomposition" false

coreWeaveAccountingLifePaid : FinalProducer
coreWeaveAccountingLifePaid = finalProducer
  "CoreWeave technology-equipment accounting-life coordinate" paid "CoreWeave 2025 Form 10-K"
  "technology equipment has a six-year estimated accounting useful life after a 2023 five-to-six-year estimate change; ordinary maintenance/repairs not extending lives are expensed" false

coreWeaveNamedPayerCapacityPaid : FinalProducer
coreWeaveNamedPayerCapacityPaid = finalProducer
  "selected CoreWeave named-payer external-cash capacity" paid "CoreWeave -> Microsoft"
  "CoreWeave discloses up to USD 43.8B of conditional Microsoft payments through 2033; Microsoft FY2026 independently reports USD 182.9B operating cash flow and USD 214.4B cloud revenue with increased customer cash receipts" false

coreWeaveNamedPayerSaturationPaid : FinalProducer
coreWeaveNamedPayerSaturationPaid = finalProducer
  "CoreWeave named-payer edge saturation" paid "Microsoft + Meta + OpenAI named contractual edges"
  "Microsoft and Meta have independently source-paid external-customer cash-generation capacity; OpenAI has a source-paid named contract edge but no equivalent public cash-provenance receipt here; realised Q2 top-three identities remain anonymised" false

terminalPayerConsumerIndexingPaid : FinalProducer
terminalPayerConsumerIndexingPaid = finalProducer
  "consumer-relative terminal-payer sufficiency" paid "selected-payer vs exhaustive-independence questions"
  "named-payer external-cash evidence pays selected edge consumers while exhaustive CoreWeave terminal independence remains a separate open consumer" false

terminalPayerStillPartial : FinalProducer
terminalPayerStillPartial = finalProducer
  "complete independent terminal-payer provenance" partial "CoreWeave/entity/global"
  "Microsoft and Meta external-cash edges are paid and OpenAI contract identity is paid, but contract realisation, OpenAI external cash, current anonymised top-customer identities and all remaining financing/counterparty loops are not exhaustively traced" false

replacementObsolescenceStillPartial : FinalProducer
replacementObsolescenceStillPartial = finalProducer
  "replacement / obsolescence burden" partial "CoreWeave H1-2026 + 2025 Form 10-K"
  "aggregate capex non-identifiability is now proved and six-year accounting life plus maintenance treatment are source-paid; installed-age distribution, retirement/refresh history, economic-obsolescence calibration and capitalised replacement amount remain open" false

policyCausalAdmissionStillPartial : FinalProducer
policyCausalAdmissionStillPartial = finalProducer
  "policy burden -> market-structure causal admission" partial "Australian AI policy lane"
  "proposal/outcome/survey substrate is paid; realised same-basis compliance costs, observed entry/concentration response and a separately reviewed causal bridge remain open; intentional capture remains a distinct claim" false

wholeComplexMarketDynamicsStillPartial : FinalProducer
wholeComplexMarketDynamicsStillPartial = finalProducer
  "whole-complex market dynamics" partial "public equities + broad market/IPO/credit evidence"
  "private labs, credit, SPVs and non-public infrastructure positions are not one harmonised fixed market basket" false

globalOpenWeightTrajectoryStillOpen : FinalProducer
globalOpenWeightTrajectoryStillOpen = finalProducer
  "global open-weight usage trajectory" open "global market"
  "Vercel trajectory is platform-local and cannot establish global usage share" false

sameCapabilityScarcityRentStillOpen : FinalProducer
sameCapabilityScarcityRentStillOpen = finalProducer
  "same-capability open/closed scarcity rent" open "global model market"
  "benchmark-normalised selected-pair pricing does not establish equal capability; the same-model engineering comparator is hosted-open versus self-hosted-open and therefore does not supply a closed/open scarcity-rent pair" false

providerServingMarginStillPartial : FinalProducer
providerServingMarginStillPartial = finalProducer
  "quality-adjusted provider serving margin" partial "provider economics"
  "same-model engineering serving-cost substitution is observed for one configuration, but the hosted provider's own marginal-cost ledger, matched SLA/cache/utilisation policy and quality-adjusted closed/open provider margin remain absent" false

numericROICWACCStillOpen : FinalProducer
numericROICWACCStillOpen = finalProducer
  "numerical realised ROIC-WACC" open "CoreWeave/global"
  "the sign-only CoreWeave spread is closed under declared conditions, but a numerical point still requires a fixed invested-capital convention, equity cost and capital weights" false

------------------------------------------------------------------------
-- Proof receipts and non-promotion.
------------------------------------------------------------------------

selectedBasketFlipPaid : Basket.selectedBasketFlipRateClosed Basket.selectedAICapitalBasketResult ≡ true
selectedBasketFlipPaid = Basket.selectedFlipRateIsClosed

selectedBasketVolPaid : Basket.selectedBasketVolatilityClosed Basket.selectedAICapitalBasketResult ≡ true
selectedBasketVolPaid = Basket.selectedVolatilityIsClosed

openTrajectoryPaid : OpenTrajectory.platformLocalPersistenceObserved OpenTrajectory.vercelOpenWeightTrajectory ≡ true
openTrajectoryPaid = OpenTrajectory.platformPersistenceIsObserved

openTrajectoryStillNotGlobal : OpenTrajectory.globalMarketTrajectoryClosed OpenTrajectory.vercelOpenWeightTrajectory ≡ false
openTrajectoryStillNotGlobal = OpenTrajectory.globalTrajectoryStillOpen

qualityPricePairPaid : QualityPrice.selectedPairClosed QualityPrice.mimoVsOpusBenchmarkPricePair ≡ true
qualityPricePairPaid = QualityPrice.selectedPairIsPaid

qualityPricePairStillNotMargin : QualityPrice.providerMarginClosed QualityPrice.mimoVsOpusBenchmarkPricePair ≡ false
qualityPricePairStillNotMargin = QualityPrice.providerMarginStillOpen

sameModelEngineeringComparatorPaid :
  SelfHostCost.sameModelIdentity SelfHostCost.miniMaxM3EngineeringComparison ≡ true
sameModelEngineeringComparatorPaid = SelfHostCost.sameModelIdentityPaid

sameModelProviderMarginStillOpen :
  SelfHostCost.directProviderMarginalCostObserved SelfHostCost.miniMaxM3EngineeringComparison ≡ false
sameModelProviderMarginStillOpen = SelfHostCost.providerMarginalCostStillUnobserved

headlineSurfaceStillInsufficient :
  CapitalObserver.headlineSurfaceSufficientForRecovery CapitalObserver.canonicalCapitalObserverBoundary ≡ false
headlineSurfaceStillInsufficient = CapitalObserver.headlineSurfaceSufficiencyRemainsFalse

coreWeaveTwoSidedObserved : Concentration.twoSidedConcentrationObserved Concentration.coreWeaveTwoSidedConcentration ≡ true
coreWeaveTwoSidedObserved = refl

coreWeaveTwoSidedStillNotTerminal : Concentration.terminalPayerIndependenceClosed Concentration.coreWeaveTwoSidedConcentration ≡ false
coreWeaveTwoSidedStillNotTerminal = Concentration.terminalIndependenceStillOpen

coreWeaveDebtCostPaid : DebtCost.debtCostSurfaceClosed DebtCost.coreWeaveDebtCostBoundary ≡ true
coreWeaveDebtCostPaid = DebtCost.debtSurfaceIsPaid

coreWeaveWACCStillOpen : DebtCost.waccClosed DebtCost.coreWeaveDebtCostBoundary ≡ false
coreWeaveWACCStillOpen = DebtCost.waccStillOpen

coreWeaveCapitalSpreadSignClosed :
  CapitalSign.signClosedUnderDeclaredConditions CapitalSign.coreWeaveCapitalSpreadClosure ≡ true
coreWeaveCapitalSpreadSignClosed = refl

coreWeaveNumericROICStillOpen :
  CapitalSign.numericROICClosed CapitalSign.coreWeaveCapitalSpreadClosure ≡ false
coreWeaveNumericROICStillOpen = CapitalSign.numericROICStillOpen

coreWeaveNumericWACCStillOpen :
  CapitalSign.numericWACCClosed CapitalSign.coreWeaveCapitalSpreadClosure ≡ false
coreWeaveNumericWACCStillOpen = CapitalSign.numericWACCStillOpen

coreWeaveCashFundingShortfallIs10454 :
  Reinvestment.cashFundingShortfallMillionUSD Reinvestment.coreWeaveH12026ReinvestmentCoverage ≡ 10454
coreWeaveCashFundingShortfallIs10454 = Reinvestment.coreWeaveCashFundingShortfallIs10454

coreWeaveReplacementCapexStillOpen :
  Reinvestment.replacementCapexIdentified Reinvestment.coreWeaveH12026ReinvestmentCoverage ≡ false
coreWeaveReplacementCapexStillOpen = Reinvestment.coreWeaveReplacementCapexStillUnidentified

coreWeaveCapexCollisionPaid : CapexDecomposition.aggregateCapexCollisionPaid ≡ true
coreWeaveCapexCollisionPaid = refl

coreWeaveAssetLifePaid :
  AssetLife.currentUsefulLifeMonths AssetLife.coreWeaveTechnologyEquipmentLife ≡ 72
coreWeaveAssetLifePaid = AssetLife.technologyEquipmentUsefulLifeMonthsIs72

coreWeaveInstalledAgeStillOpen :
  AssetLife.installedAgeDistributionIdentified AssetLife.coreWeaveTechnologyEquipmentLife ≡ false
coreWeaveInstalledAgeStillOpen = AssetLife.installedAgeDistributionStillOpen

coreWeaveMicrosoftExternalCashCapacityPaid :
  TerminalPayer.selectedNamedPayerExternalCashCapacity TerminalPayer.coreWeaveMicrosoftTerminalPayerBoundary ≡ true
coreWeaveMicrosoftExternalCashCapacityPaid = TerminalPayer.selectedNamedPayerCapacityIsPaid

coreWeaveMetaExternalCashCapacityPaid :
  PayerSaturation.externalCustomerCashObserved PayerSaturation.metaEdge ≡ true
coreWeaveMetaExternalCashCapacityPaid = PayerSaturation.metaExternalCashEdgePaid

coreWeaveOpenAIExternalCashStillOpen :
  PayerSaturation.externalCustomerCashObserved PayerSaturation.openAIEdge ≡ false
coreWeaveOpenAIExternalCashStillOpen = PayerSaturation.openAIExternalCashStillOpen

coreWeaveCurrentTopCustomerIdentityStillOpen :
  PayerSaturation.currentTopThreeIdentitiesPaid PayerSaturation.coreWeavePayerSaturation ≡ false
coreWeaveCurrentTopCustomerIdentityStillOpen = PayerSaturation.anonymousCurrentTopCustomerIdentityStillOpen

coreWeaveCompleteTerminalPayerStillOpen :
  TerminalPayer.completeTerminalPayerProvenanceClosed TerminalPayer.coreWeaveMicrosoftTerminalPayerBoundary ≡ false
coreWeaveCompleteTerminalPayerStillOpen = TerminalPayer.completeTerminalPayerProvenanceStillOpen

selectedPayerConsumerPaid :
  PayerConsumer.consumerPaymentState PayerConsumer.selectedMicrosoftExternalCashCapacity ≡ PayerConsumer.paid
selectedPayerConsumerPaid = PayerConsumer.selectedMicrosoftCapacityConsumerPaid

exhaustivePayerConsumerStillOpen :
  PayerConsumer.consumerPaymentState PayerConsumer.exhaustiveCoreWeaveTerminalIndependence ≡ PayerConsumer.open
exhaustivePayerConsumerStillOpen = PayerConsumer.coreWeaveExhaustiveIndependenceConsumerOpen

policySameBasisBurdenStillOpen : PolicyCausal.sameBasisBurdenMeasurementStillOpen ≡ true
policySameBasisBurdenStillOpen = refl

policyReviewedCausalBridgeStillOpen : PolicyCausal.reviewedCausalBridgeStillOpen ≡ true
policyReviewedCausalBridgeStillOpen = refl

policyIntentionalCaptureStillSeparate : PolicyCausal.intentionalCaptureStillSeparate ≡ true
policyIntentionalCaptureStillSeparate = refl

data ScopedPaymentImpliesGlobalClosurePermission : Set where
data PriceNormalizationImpliesMarginPermission : Set where
data ConcentrationTopologyImpliesTerminalPayerPermission : Set where
data DebtCostImpliesWACCPermission : Set where
data SignOnlySpreadImpliesNumericSpreadPermission : Set where
data CapexGapImpliesReplacementCapexPermission : Set where
data AccountingLifeImpliesEconomicObsolescencePermission : Set where
data EngineeringServingCostImpliesProviderMarginPermission : Set where
data NamedPayerEdgesImpliesCompleteTerminalPayerPermission : Set where
data PolicyFactsImpliesCausalConcentrationPermission : Set where

scopedPaymentDoesNotAutoCloseGlobal : ScopedPaymentImpliesGlobalClosurePermission → ⊥
scopedPaymentDoesNotAutoCloseGlobal ()

priceNormalizationDoesNotAutoCreateMargin : PriceNormalizationImpliesMarginPermission → ⊥
priceNormalizationDoesNotAutoCreateMargin ()

concentrationTopologyDoesNotAutoCreateTerminalPayer : ConcentrationTopologyImpliesTerminalPayerPermission → ⊥
concentrationTopologyDoesNotAutoCreateTerminalPayer ()

debtCostDoesNotAutoCreateWACC : DebtCostImpliesWACCPermission → ⊥
debtCostDoesNotAutoCreateWACC ()

signOnlySpreadDoesNotAutoCreateNumericSpread : SignOnlySpreadImpliesNumericSpreadPermission → ⊥
signOnlySpreadDoesNotAutoCreateNumericSpread ()

capexGapDoesNotAutoIdentifyReplacementCapex : CapexGapImpliesReplacementCapexPermission → ⊥
capexGapDoesNotAutoIdentifyReplacementCapex ()

accountingLifeDoesNotCreateEconomicObsolescence : AccountingLifeImpliesEconomicObsolescencePermission → ⊥
accountingLifeDoesNotCreateEconomicObsolescence ()

engineeringServingCostDoesNotCreateProviderMargin : EngineeringServingCostImpliesProviderMarginPermission → ⊥
engineeringServingCostDoesNotCreateProviderMargin ()

namedPayerEdgesDoNotCloseCompleteTerminalProvenance :
  NamedPayerEdgesImpliesCompleteTerminalPayerPermission → ⊥
namedPayerEdgesDoNotCloseCompleteTerminalProvenance ()

policyFactsDoNotCreateCausalConcentration :
  PolicyFactsImpliesCausalConcentrationPermission → ⊥
policyFactsDoNotCreateCausalConcentration ()

finalBoundary : String
finalBoundary =
  "After the October-12 max-cut, selected public-equity dynamics, Vercel open-weight persistence, benchmark-normalised open/closed price evidence, a same-model hosted/self-host engineering-cost comparator, and an exact headline-observer non-descent theorem are paid. CoreWeave now has paid concentration/debt/sign-only capital spread/internal-cash shortfall, constructive capex-decomposition non-identifiability, six-year accounting-life evidence, Microsoft and Meta external-cash payer edges, and an OpenAI named contractual edge with cash provenance still open. Consumer-relative sufficiency and edge-local provenance prevent those strong edges from becoming exhaustive terminal independence. Replacement/obsolescence remains partial at installed-age/refresh/economic-life coordinates. Provider serving margin remains partial because provider-owned marginal cost is absent. The Australian policy lane still requires same-basis realised compliance costs, observed market response and a reviewed causal bridge. Numerical ROIC/WACC and exhaustive terminal capital recovery remain open."
