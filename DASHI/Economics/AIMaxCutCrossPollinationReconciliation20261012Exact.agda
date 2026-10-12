module DASHI.Economics.AIMaxCutCrossPollinationReconciliation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Economics.AIMaxCutReconciliation20261012FinalExact as Prior
import DASHI.Economics.AICapitalObserverNonDescent20261012Exact as NonDescent
import DASHI.Economics.AICapitalBurdenRelocation20261012Exact as Relocation
import DASHI.Economics.AISelectedInferenceCrackSpread20261012Exact as Crack
import DASHI.Economics.AICoreWeaveNamedPayerSaturation20261012Exact as Payer
import DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact as SameModel
import DASHI.Economics.AICerebrasCloudMarginObserverBoundary20261012Exact as CerebrasMargin

------------------------------------------------------------------------
-- CROSS-POLLINATION RECONCILIATION
--
-- Records the highest-alpha transfers from the repository's canonical
-- consumer-descent/fibre-repair, accounting-flow and observer-basis disciplines
-- into the October-2026 AI-capital programme. All payments remain scoped.
------------------------------------------------------------------------

data XPState : Set where
  open partial paid : XPState

record XPProducer : Set where
  constructor xp-producer
  field
    producer : String
    state : XPState
    scope : String
    receipt : String
    createsGlobalCapitalRecoveryAuthority : Bool

open XPProducer public

headlineObserverNonDescentPaid : XPProducer
headlineObserverNonDescentPaid = xp-producer
  "headline-observer non-descent"
  paid
  "synthetic finite capital worlds / canonical consumer-descent theorem"
  "identical revenue/usage/valuation/market-price surface can hide different recovery outcomes through terminal-payer or capital-spread coordinates; every sufficient repair must separate the witnessed fibre collision"
  false

capitalBurdenRelocationPaid : XPProducer
capitalBurdenRelocationPaid = xp-producer
  "provider-to-customer capital-burden relocation"
  paid
  "generic accounting transform with Oracle USD 75B scale receipt"
  "provider funding need may fall while customer committed capital rises by the same amount; system burden need not disappear"
  false

selectedInferenceCrackSpreadPaid : XPProducer
selectedInferenceCrackSpreadPaid = xp-producer
  "selected same-model inference crack spread"
  paid
  "MiniMax-M3 declared engineering configuration"
  "USD 1.20/M hosted versus USD 0.93/M estimated self-host gives USD 0.27/M buyer-side spread, 22.5 percent of hosted price"
  false

cerebrasAccountingCloudMarginsPaid : XPProducer
cerebrasAccountingCloudMarginsPaid = xp-producer
  "Cerebras cloud-and-other-services accounting margin observations"
  paid
  "Cerebras Q2-2026 GAAP and company-defined core/non-GAAP observers"
  "GAAP cloud/services gross margin is 19.5 percent versus 25.6 percent Q2-2025 while core cloud/services gross margin is 41.8 percent versus 26.0 percent; opposite directions are retained as accounting-basis dependence, not collapsed"
  false

namedExternalCashEdgesPartial : XPProducer
namedExternalCashEdgesPartial = xp-producer
  "CoreWeave named-payer external-cash saturation"
  partial
  "Microsoft + Meta paid external-cash-capacity edges; OpenAI contract edge only"
  "two named payer edges have independent external-customer cash-generation capacity; realised top-three customer identities and OpenAI external-cash provenance remain unresolved"
  false

providerMarginStillOpen : XPProducer
providerMarginStillOpen = xp-producer
  "provider marginal serving margin"
  open
  "provider economics"
  "same-model engineering substitution cost, buyer-side hosted spread, and Cerebras segment accounting margins are paid, but no pure inference provider marginal-cost ledger or matched quality-adjusted marginal serving margin is observed"
  false

exhaustiveTerminalPayerStillOpen : XPProducer
exhaustiveTerminalPayerStillOpen = xp-producer
  "exhaustive terminal-payer provenance"
  open
  "CoreWeave/global payer graph"
  "selected named external-cash edges do not identify anonymised realised top customers, contract realisation, or every financing/counterparty loop"
  false

------------------------------------------------------------------------
-- Cross-owner receipts.
------------------------------------------------------------------------

headlineNonDescentBlocksFactorization :
  Descent.FactorsThrough
    NonDescent.headlineObserver
    NonDescent.capitalRecoveryConsumer → ⊥
headlineNonDescentBlocksFactorization =
  NonDescent.headlineMetricsDoNotAutoFactorCapitalRecovery

relocationBeforeBurdenPaid :
  Relocation.systemBurdenBillionUSD Relocation.illustrativeBefore ≡ 75
relocationBeforeBurdenPaid = Relocation.illustrativeBeforeSystemBurdenIs75

relocationAfterBurdenPaid :
  Relocation.systemBurdenBillionUSD Relocation.illustrativeAfter ≡ 75
relocationAfterBurdenPaid = Relocation.illustrativeAfterSystemBurdenIs75

selectedCrackSpreadIs27c :
  Crack.buyerSpreadCentsPerMillionOutput Crack.miniMaxM3SelectedCrackSpread ≡ 27
selectedCrackSpreadIs27c = Crack.selectedHostingSpreadCentsIs27

selectedCrackSpreadIs2250bp :
  Crack.buyerSpreadShareBpOfHostedPrice Crack.miniMaxM3SelectedCrackSpread ≡ 2250
selectedCrackSpreadIs2250bp = Crack.selectedHostingSpreadShareBpIs2250

cerebrasGaapCloudMarginIs1950bp :
  CerebrasMargin.laterMarginBp CerebrasMargin.cerebrasGaapCloudMargin ≡ 1950
cerebrasGaapCloudMarginIs1950bp = CerebrasMargin.q22026GaapCloudMarginIs1950bp

cerebrasCoreCloudMarginIs4180bp :
  CerebrasMargin.laterMarginBp CerebrasMargin.cerebrasCoreCloudMargin ≡ 4180
cerebrasCoreCloudMarginIs4180bp = CerebrasMargin.q22026CoreCloudMarginIs4180bp

cerebrasMarginalInferenceMarginStillOpen :
  CerebrasMargin.marginalInferenceServingMarginPaid CerebrasMargin.cerebrasGaapCloudMargin ≡ false
cerebrasMarginalInferenceMarginStillOpen = CerebrasMargin.marginalInferenceServingMarginStillOpen

sameModelStillNotProviderMargin :
  SameModel.directProviderMarginalCostObserved SameModel.miniMaxM3EngineeringComparison ≡ false
sameModelStillNotProviderMargin = SameModel.providerMarginalCostStillUnobserved

namedPayerGraphStillNotExhaustive :
  Payer.exhaustiveTerminalGraphClosed Payer.coreWeavePayerSaturation ≡ false
namedPayerGraphStillNotExhaustive = refl

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data NonDescentImpliesNamedFirmFailurePermission : Set where
data RelocationImpliesNoNewCapitalPermission : Set where
data BuyerSpreadImpliesProviderMarginPermission : Set where
data AccountingSegmentMarginImpliesMarginalServingMarginPermission : Set where
data NamedEdgesImpliesWholeGraphPermission : Set where

nonDescentDoesNotCreateNamedFirmFailure :
  NonDescentImpliesNamedFirmFailurePermission → ⊥
nonDescentDoesNotCreateNamedFirmFailure ()

burdenRelocationDoesNotProveNoNewCapital :
  RelocationImpliesNoNewCapitalPermission → ⊥
burdenRelocationDoesNotProveNoNewCapital ()

buyerSpreadDoesNotCreateProviderMargin :
  BuyerSpreadImpliesProviderMarginPermission → ⊥
buyerSpreadDoesNotCreateProviderMargin ()

accountingSegmentMarginDoesNotCreateMarginalServingMargin :
  AccountingSegmentMarginImpliesMarginalServingMarginPermission → ⊥
accountingSegmentMarginDoesNotCreateMarginalServingMargin ()

namedEdgesDoNotCreateWholeGraph :
  NamedEdgesImpliesWholeGraphPermission → ⊥
namedEdgesDoNotCreateWholeGraph ()

boundary : String
boundary =
  "The latest cross-pollination cut proves headline-only AI observables are not consumer-sufficient for capital recovery, formalises capital-burden relocation, pays a selected 22.5-percent buyer-side same-model hosting spread, pays Cerebras cloud/services accounting-margin observers while preserving their opposite GAAP/core directions, and narrows CoreWeave terminal-payer provenance to a smaller unresolved tail. Pure inference provider marginal serving cost/margin, exhaustive payer provenance and global capital-recovery authority remain open."
