{-# OPTIONS --safe #-}
module DASHI.Interop.SLRFullWorkspaceCrateCoverageExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SLRPostgresWorldPersistenceExact as PG
import DASHI.Interop.SLRProtectedPNFFleetReductionExact as Fleet
import DASHI.Interop.SLRActorCriticPromotionExact as Critic
import DASHI.Interop.SLRSharedEvidenceReducerExact as Evidence
import DASHI.Interop.SLRProductionRoadmapParityExact as Roadmap

-- Finite crate inventory. Carrier strings are descriptive specification
-- labels. This is not a verified mapping to the Rust workspace manifest.
data SLRCrateLayer : Set where
  verificationAndCLI : SLRCrateLayer
  coreCarrier : SLRCrateLayer
  worldIngestionAndCompiler : SLRCrateLayer
  residualAndRoutePlanning : SLRCrateLayer
  evidenceReviewAndPayment : SLRCrateLayer
  formalProofAndReopen : SLRCrateLayer
  legalRuntimeAndProviders : SLRCrateLayer

data SLRCarrierKind : Set where
  benchmarkFixture : SLRCarrierKind
  throughputReceipt : SLRCarrierKind
  cliCommandArgs : SLRCarrierKind
  cliProjectionOutput : SLRCarrierKind
  referenceFixture : SLRCarrierKind
  parityAuditReceipt : SLRCarrierKind
  sourceSpanStream : SLRCarrierKind
  canonicalAtomIdAndPnfUnit : SLRCarrierKind
  readerProjectionCarrier : SLRCarrierKind
  segmentedTokenStream : SLRCarrierKind
  pgCorpusMessageRow : SLRCarrierKind
  sourceAnchorAndDocumentUnit : SLRCarrierKind
  wikimediaRevisionDump : SLRCarrierKind
  externalCandidateBridge : SLRCarrierKind
  candidateWorldModel : SLRCarrierKind
  expandedWorldCandidate : SLRCarrierKind
  pgWorldModelProjection : SLRCarrierKind
  consumerResidualVector : SLRCarrierKind
  proofSearchTrace : SLRCarrierKind
  scheduledSearchFrontier : SLRCarrierKind
  residualRepairPlan : SLRCarrierKind
  selectedRoutePlan : SLRCarrierKind
  routeExecutionReceipt : SLRCarrierKind
  admissionCandidateReceipt : SLRCarrierKind
  semanticStatusSummary : SLRCarrierKind
  evidencePaymentLedger : SLRCarrierKind
  reopenTriggerReceipt : SLRCarrierKind
  certificateCandidate : SLRCarrierKind
  reviewedPaymentReceipt : SLRCarrierKind
  kernelVerificationObligation : SLRCarrierKind
  legalSourceDocument : SLRCarrierKind
  legalProvisionCandidate : SLRCarrierKind
  counterfactualObligationSlice : SLRCarrierKind
  legalFollowGraphPlan : SLRCarrierKind
  obligationAlignmentReceipt : SLRCarrierKind
  nswLegislationXml : SLRCarrierKind

data SLRCrateId : Set where
  slBench : SLRCrateId
  slCli : SLRCrateId
  slParity : SLRCrateId
  slCore : SLRCrateId
  slReaderModel : SLRCrateId
  slStream : SLRCrateId
  slPgSourceStore : SLRCrateId
  slWikimediaCandidateProvider : SLRCrateId
  slWorldCompiler : SLRCrateId
  slWorldExpansionRuntime : SLRCrateId
  slWorldStore : SLRCrateId
  slConsumerResidual : SLRCrateId
  slProofSearchLoop : SLRCrateId
  slProofSearchScheduler : SLRCrateId
  slResidualPlanner : SLRCrateId
  slRouteExecutor : SLRCrateId
  slRouteSelector : SLRCrateId
  slSemanticAdmission : SLRCrateId
  slSemanticExpansion : SLRCrateId
  slSemanticStatus : SLRCrateId
  slEvidencePayment : SLRCrateId
  slEvidentialReopen : SLRCrateId
  slExpandedCert : SLRCrateId
  slReviewedEvidencePayment : SLRCrateId
  slFormalProofBridge : SLRCrateId
  slFormalProofReopen : SLRCrateId
  slGovernedLegalProvider : SLRCrateId
  slLegalCounterfactual : SLRCrateId
  slLegalFollowPlan : SLRCrateId
  slLegalRuntime : SLRCrateId
  slNswLegislationProvider : SLRCrateId

record SLRCrateContract : Set where
  constructor crateContract
  field
    crateName : String
    layer : SLRCrateLayer
    inputCarrier : SLRCarrierKind
    outputCarrier : SLRCarrierKind
    createsSemanticTruth : Bool
    requiresReviewedOrKernelGate : Bool

slrCrateSpec : SLRCrateId → SLRCrateContract
slrCrateSpec slBench = crateContract "sl-bench" verificationAndCLI benchmarkFixture throughputReceipt false false
slrCrateSpec slCli = crateContract "sl-cli" verificationAndCLI cliCommandArgs cliProjectionOutput false false
slrCrateSpec slParity = crateContract "sl-parity" verificationAndCLI referenceFixture parityAuditReceipt false false
slrCrateSpec slCore = crateContract "sl-core" coreCarrier sourceSpanStream canonicalAtomIdAndPnfUnit false false
slrCrateSpec slReaderModel = crateContract "sl-reader-model" coreCarrier canonicalAtomIdAndPnfUnit readerProjectionCarrier false false
slrCrateSpec slStream = crateContract "sl-stream" coreCarrier sourceSpanStream segmentedTokenStream false false
slrCrateSpec slPgSourceStore = crateContract "sl-pg-source-store" worldIngestionAndCompiler pgCorpusMessageRow sourceAnchorAndDocumentUnit false false
slrCrateSpec slWikimediaCandidateProvider = crateContract "sl-wikimedia-candidate-provider" worldIngestionAndCompiler wikimediaRevisionDump externalCandidateBridge false false
slrCrateSpec slWorldCompiler = crateContract "sl-world-compiler" worldIngestionAndCompiler sourceAnchorAndDocumentUnit candidateWorldModel false false
slrCrateSpec slWorldExpansionRuntime = crateContract "sl-world-expansion-runtime" worldIngestionAndCompiler candidateWorldModel expandedWorldCandidate false false
slrCrateSpec slWorldStore = crateContract "sl-world-store" worldIngestionAndCompiler candidateWorldModel pgWorldModelProjection false false
slrCrateSpec slConsumerResidual = crateContract "sl-consumer-residual" residualAndRoutePlanning candidateWorldModel consumerResidualVector false false
slrCrateSpec slProofSearchLoop = crateContract "sl-proof-search-loop" residualAndRoutePlanning consumerResidualVector proofSearchTrace false false
slrCrateSpec slProofSearchScheduler = crateContract "sl-proof-search-scheduler" residualAndRoutePlanning proofSearchTrace scheduledSearchFrontier false false
slrCrateSpec slResidualPlanner = crateContract "sl-residual-planner" residualAndRoutePlanning consumerResidualVector residualRepairPlan false false
slrCrateSpec slRouteExecutor = crateContract "sl-route-executor" residualAndRoutePlanning selectedRoutePlan routeExecutionReceipt false false
slrCrateSpec slRouteSelector = crateContract "sl-route-selector" residualAndRoutePlanning residualRepairPlan selectedRoutePlan false false
slrCrateSpec slSemanticAdmission = crateContract "sl-semantic-admission" residualAndRoutePlanning expandedWorldCandidate admissionCandidateReceipt false false
slrCrateSpec slSemanticExpansion = crateContract "sl-semantic-expansion" residualAndRoutePlanning candidateWorldModel expandedWorldCandidate false false
slrCrateSpec slSemanticStatus = crateContract "sl-semantic-status" residualAndRoutePlanning admissionCandidateReceipt semanticStatusSummary false false
slrCrateSpec slEvidencePayment = crateContract "sl-evidence-payment" evidenceReviewAndPayment admissionCandidateReceipt evidencePaymentLedger false true
slrCrateSpec slEvidentialReopen = crateContract "sl-evidential-reopen" evidenceReviewAndPayment evidencePaymentLedger reopenTriggerReceipt false true
slrCrateSpec slExpandedCert = crateContract "sl-expanded-cert" evidenceReviewAndPayment expandedWorldCandidate certificateCandidate false true
slrCrateSpec slReviewedEvidencePayment = crateContract "sl-reviewed-evidence-payment" evidenceReviewAndPayment evidencePaymentLedger reviewedPaymentReceipt false true
slrCrateSpec slFormalProofBridge = crateContract "sl-formal-proof-bridge" formalProofAndReopen certificateCandidate kernelVerificationObligation false true
slrCrateSpec slFormalProofReopen = crateContract "sl-formal-proof-reopen" formalProofAndReopen kernelVerificationObligation reopenTriggerReceipt false true
slrCrateSpec slGovernedLegalProvider = crateContract "sl-governed-legal-provider" legalRuntimeAndProviders legalSourceDocument legalProvisionCandidate false false
slrCrateSpec slLegalCounterfactual = crateContract "sl-legal-counterfactual" legalRuntimeAndProviders legalProvisionCandidate counterfactualObligationSlice false false
slrCrateSpec slLegalFollowPlan = crateContract "sl-legal-follow-plan" legalRuntimeAndProviders legalProvisionCandidate legalFollowGraphPlan false false
slrCrateSpec slLegalRuntime = crateContract "sl-legal-runtime" legalRuntimeAndProviders legalFollowGraphPlan obligationAlignmentReceipt false false
slrCrateSpec slNswLegislationProvider = crateContract "sl-nsw-legislation-provider" legalRuntimeAndProviders nswLegislationXml legalSourceDocument false false

record CandidateDoesNotClaimTruth (c : SLRCrateContract) : Set where
  constructor candidateDoesNotClaimTruth
  field noTruthClaim : SLRCrateContract.createsSemanticTruth c ≡ false

all31CratesDoNotSelfCertifyTruth : (c : SLRCrateId) → CandidateDoesNotClaimTruth (slrCrateSpec c)
all31CratesDoNotSelfCertifyTruth slBench = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slCli = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slParity = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slCore = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slReaderModel = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slStream = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slPgSourceStore = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slWikimediaCandidateProvider = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slWorldCompiler = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slWorldExpansionRuntime = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slWorldStore = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slConsumerResidual = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slProofSearchLoop = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slProofSearchScheduler = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slResidualPlanner = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slRouteExecutor = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slRouteSelector = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slSemanticAdmission = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slSemanticExpansion = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slSemanticStatus = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slEvidencePayment = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slEvidentialReopen = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slExpandedCert = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slReviewedEvidencePayment = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slFormalProofBridge = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slFormalProofReopen = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slGovernedLegalProvider = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slLegalCounterfactual = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slLegalFollowPlan = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slLegalRuntime = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth slNswLegislationProvider = candidateDoesNotClaimTruth refl
