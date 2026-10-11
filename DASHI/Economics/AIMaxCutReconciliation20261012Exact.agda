module DASHI.Economics.AIMaxCutReconciliation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICapitalAcquisitionProgress20261008Exact as Progress
import DASHI.Economics.AICapitalProducerBoundedEvidence2026Exact as Bounded
import DASHI.Economics.AICounterpartyRoleOverlap2026Exact as Counterparty
import DASHI.Economics.AIInfrastructureCommitmentTrajectory2026Exact as Commitment
import DASHI.Economics.AIRegulatoryBurdenConcentrationSensibLaw2026Exact as Regulatory
import DASHI.Economics.AIAustraliaRegulatoryPolicyAcquisition20261012Exact as AustraliaPolicy
import DASHI.Economics.AIMarketOpenWeightFreshAcquisition20261012Exact as Fresh
import DASHI.Economics.AICapitalObservedStateTimeSeries2026Exact as Global

------------------------------------------------------------------------
-- TERMINAL MAX-CUT RECONCILIATION, 2026-10-12
--
-- Entity-scoped and current-market acquisitions have paid real leaves since
-- the original global residual board was created. This owner reconciles those
-- advances without promoting component/platform closure into global capital-
-- recovery authority.
------------------------------------------------------------------------

data ReconciledState : Set where
  open partial paid : ReconciledState

record ReconciledProducer : Set where
  constructor reconciledProducer
  field
    producer : String
    state : ReconciledState
    scope : String
    receipt : String
    promotesGlobalCapitalRecovery : Bool

open ReconciledProducer public

coreWeaveEntityRolloverPaid : ReconciledProducer
coreWeaveEntityRolloverPaid = reconciledProducer
  "CoreWeave rollover / maturity schedule"
  paid "entity"
  "complete stated June-30-2026 principal maturity schedule is acquired for CoreWeave"
  false

entityPersistencePaid : ReconciledProducer
entityPersistencePaid = reconciledProducer
  "same-entity persistence"
  paid "CoreWeave:H1 and Cerebras:H1"
  "fixed-key H1-2025 -> H1-2026 same-company state pairs exist"
  false

globalPersistenceStillOpen : ReconciledProducer
globalPersistenceStillOpen = reconciledProducer
  "global AI-capital persistence"
  open "global complex"
  "global graph/fundamental coverage changed; no second comparable whole-complex X_t is yet available"
  false

cerebrasRoleOverlapPaid : ReconciledProducer
cerebrasRoleOverlapPaid = reconciledProducer
  "Cerebras named multi-role counterparty revenue lower bound"
  paid "entity / selected counterparties"
  ">= 7,892 bp of H1-2026 revenue is source-backed to named counterparties with multiple economic roles"
  false

terminalPayerIndependenceStillOpen : ReconciledProducer
terminalPayerIndependenceStillOpen = reconciledProducer
  "independent terminal-payer provenance"
  open "global and entity terminal payer"
  "customer concentration and multi-role counterparty receipts do not establish independent external terminal cash"
  false

infrastructureCommitmentTrajectoryPaid : ReconciledProducer
infrastructureCommitmentTrajectoryPaid = reconciledProducer
  "source-backed infrastructure commitment trajectories"
  paid "selected companies / heterogeneous accounting scopes"
  "NVIDIA same-metric supply/capacity trajectory and Oracle/Microsoft/Alphabet commitment disclosures are acquired with non-additivity firewall"
  false

realisedROICWACCStillOpen : ReconciledProducer
realisedROICWACCStillOpen = reconciledProducer
  "realised ROIC-WACC capital spread"
  open "entity and global"
  "operating/cash-flow trajectories exist, but an admissible same-entity realised ROIC and WACC join remains absent"
  false

qualityAdjustedInferenceMarginStillOpen : ReconciledProducer
qualityAdjustedInferenceMarginStillOpen = reconciledProducer
  "quality-adjusted inference margin"
  partial "platform-direction evidence"
  "token-price direction is observed; same-quality realised serving revenue minus marginal serving cost is not"
  false

openWeightPlatformPointPaid : ReconciledProducer
openWeightPlatformPointPaid = reconciledProducer
  "current open-weight token-volume share"
  paid "Vercel AI Gateway platform-local point"
  "2026-10-10 leaderboard reports 61.3 percent open-weight versus 38.7 percent closed-weight token volume; global market share remains unproved"
  false

scarcityCapabilityCompressionStillPartial : ReconciledProducer
scarcityCapabilityCompressionStillPartial = reconciledProducer
  "capability-normalised scarcity-rent compression"
  partial "platform/open-weight evidence"
  "current 61.3 percent Vercel open-weight token-volume point strengthens substitution evidence; same-quality global scarcity-rent point remains absent"
  false

replacementObsolescenceStillPartial : ReconciledProducer
replacementObsolescenceStillPartial = reconciledProducer
  "replacement / depreciation / obsolescence"
  partial "lender/economic-life evidence"
  "3-4 year lender GPU depreciation assumptions are acquired; entity-specific replacement capex remains open"
  false

marketEventEvidenceNowPartial : ReconciledProducer
marketEventEvidenceNowPartial = reconciledProducer
  "market flip / volatility evidence"
  partial "broad-index event series plus AI financing-window event"
  "Oct-8 Nasdaq/S&P decline followed by Oct-9 rebound and Firmus AI-infrastructure IPO withdrawal supply current stress/direction evidence; fixed-composition AI basket series and volatility remain open"
  false

australiaPolicyTrajectoryPaid : ReconciledProducer
australiaPolicyTrajectoryPaid = reconciledProducer
  "Australian high-risk-AI guardrail policy trajectory"
  paid "selected Australian policy lane"
  "mandatory-guardrails proposal and regulatory-impact survey are acquired; government currently states the previous mandatory proposal will not proceed at this time while voluntary/guidance machinery persists"
  false

regulatoryMeasuredBurdenStillOpen : ReconciledProducer
regulatoryMeasuredBurdenStillOpen = reconciledProducer
  "measured regulatory compliance burden / concentration response"
  open "policy-economy"
  "structural moat mechanism and an observed Australian policy trajectory exist, but a same-basis compliance-cost vector and observed entry/open-weight/concentration response remain unacquired"
  false

------------------------------------------------------------------------
-- Cross-owner proof receipts.
------------------------------------------------------------------------

coreWeaveRolloverReusesPaidEntityLeaf :
  Progress.closure Progress.coreWeaveRolloverProgress ≡ Progress.closed
coreWeaveRolloverReusesPaidEntityLeaf = Progress.coreWeaveEntityRolloverIsClosed

entityPersistenceReusesPaidLeaf :
  Progress.closure Progress.entityPersistenceProgress ≡ Progress.closed
entityPersistenceReusesPaidLeaf = Progress.entityPersistenceIsClosed

globalPersistenceReusesOpenLeaf :
  Progress.closure Progress.globalPersistenceProgress ≡ Progress.open
globalPersistenceReusesOpenLeaf = Progress.globalPersistenceStillOpen

cerebrasRoleOverlapLowerBoundIs7892bp :
  Counterparty.namedMultiRoleRevenueLowerBoundBp
    Counterparty.cerebrasNamedRoleOverlapLowerBound ≡ 7892
cerebrasRoleOverlapLowerBoundIs7892bp =
  Counterparty.cerebrasRoleOverlapLowerBoundIs7892bp

terminalIndependenceNotManufacturedByRoleOverlap :
  Counterparty.terminalIndependenceEstablished
    Counterparty.cerebrasNamedRoleOverlapLowerBound ≡ false
terminalIndependenceNotManufacturedByRoleOverlap = refl

oracleCustomerFundingStillNotTerminalCash :
  Commitment.establishesIndependentTerminalCash
    Commitment.oracleCustomerFundedAIHardware ≡ false
oracleCustomerFundingStillNotTerminalCash =
  Commitment.oracleCustomerFundingStillNotTerminal

inferencePointStillOpen :
  Bounded.pointProducerClosed Bounded.inferenceSpreadEvidence ≡ false
inferencePointStillOpen = refl

scarcityPointStillOpen :
  Bounded.pointProducerClosed Bounded.scarcitySpreadEvidence ≡ false
scarcityPointStillOpen = refl

replacementPointStillOpen :
  Bounded.pointProducerClosed Bounded.gpuReplacementEvidence ≡ false
replacementPointStillOpen = refl

currentOpenWeightPlatformPointIs6130bp :
  Fresh.openWeightTokenShareBp Fresh.vercelOpenWeightSnapshot20261010 ≡ 6130
currentOpenWeightPlatformPointIs6130bp = Fresh.openWeightPointIs6130bp

currentOpenWeightPointStillNotGlobal :
  Fresh.globalMarketShareClosed Fresh.vercelOpenWeightSnapshot20261010 ≡ false
currentOpenWeightPointStillNotGlobal = Fresh.globalOpenWeightShareStillUnclosed

fixedAIBasketStillOpenAfterBroadMarketEvents :
  Fresh.fixedAIBasketSeriesClosed Fresh.currentMarketEventEvidence20261012 ≡ false
fixedAIBasketStillOpenAfterBroadMarketEvents = Fresh.fixedBasketStillUnclosed

australiaMandatoryProposalCurrentlyNotProceeding :
  AustraliaPolicy.mandatoryGuardrailsCurrentlyProceeding
    AustraliaPolicy.mandatoryGuardrailsProposalAcquired ≡ false
australiaMandatoryProposalCurrentlyNotProceeding =
  AustraliaPolicy.mandatoryProposalCurrentlyNotProceeding

regulatorySurveyStillLacksHarmonisedCostVector :
  AustraliaPolicy.harmonisedCostVectorAcquired
    AustraliaPolicy.regulatoryImpactSurveyAcquired ≡ false
regulatorySurveyStillLacksHarmonisedCostVector =
  AustraliaPolicy.sameBasisCostVectorStillOpen

regulatorySameBasisCostStillOpen :
  Regulatory.sameBasisComplianceCostsAcquired
    Regulatory.currentRegulatoryBurdenResidual ≡ false
regulatorySameBasisCostStillOpen = refl

regulatoryConcentrationResponseStillOpen :
  Regulatory.concentrationEffectObserved
    Regulatory.currentRegulatoryBurdenResidual ≡ false
regulatoryConcentrationResponseStillOpen = refl

globalStateStillNonPromotable :
  Global.promotionReady Global.currentObservedCapitalState20261007 ≡ false
globalStateStillNonPromotable = refl

------------------------------------------------------------------------
-- No-scope-jump firewalls.
------------------------------------------------------------------------

data EntityPaidImpliesGlobalPaidPermission : Set where
data CommitmentScaleImpliesCapitalRecoveryPermission : Set where
data RoleOverlapImpliesNoTerminalDemandPermission : Set where
data StructuralMoatImpliesMeasuredBurdenPermission : Set where
data ProposalOutcomeImpliesGenericMoatFalsePermission : Set where
data PlatformShareImpliesGlobalSharePermission : Set where
data BroadMarketEventsImpliesFixedAIBasketPermission : Set where

entityPaidDoesNotAutoCloseGlobal : EntityPaidImpliesGlobalPaidPermission → ⊥
entityPaidDoesNotAutoCloseGlobal ()

largeCommitmentsDoNotAutoCloseCapitalRecovery :
  CommitmentScaleImpliesCapitalRecoveryPermission → ⊥
largeCommitmentsDoNotAutoCloseCapitalRecovery ()

roleOverlapDoesNotAutoProveNoTerminalDemand :
  RoleOverlapImpliesNoTerminalDemandPermission → ⊥
roleOverlapDoesNotAutoProveNoTerminalDemand ()

structuralMoatDoesNotAutoCreateMeasuredBurden :
  StructuralMoatImpliesMeasuredBurdenPermission → ⊥
structuralMoatDoesNotAutoCreateMeasuredBurden ()

australianProposalOutcomeDoesNotRefuteGenericMoatMechanism :
  ProposalOutcomeImpliesGenericMoatFalsePermission → ⊥
australianProposalOutcomeDoesNotRefuteGenericMoatMechanism ()

platformShareDoesNotAutoCreateGlobalShare :
  PlatformShareImpliesGlobalSharePermission → ⊥
platformShareDoesNotAutoCreateGlobalShare ()

broadMarketEventsDoNotAutoCloseFixedAIBasket :
  BroadMarketEventsImpliesFixedAIBasketPermission → ⊥
broadMarketEventsDoNotAutoCloseFixedAIBasket ()

terminalBoundary : String
terminalBoundary =
  "The October-2026 tranche has paid entity rollover, entity persistence, selected counterparty-role overlap, infrastructure-commitment trajectories, one concrete Australian policy trajectory and a current Vercel open-weight platform point. Broad-market/IPO stress evidence is now partial rather than absent. It has not paid independent terminal-payer provenance, realised ROIC-WACC, global comparable persistence/rollover, quality-adjusted inference margin, capability-normalised global scarcity rent, a fixed-composition AI market basket/volatility series or measured policy compliance/concentration response."
