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

data SLRCrateId : Set where
  sl_bench : SLRCrateId
  sl_cli : SLRCrateId
  sl_parity : SLRCrateId
  sl_core : SLRCrateId
  sl_reader_model : SLRCrateId
  sl_stream : SLRCrateId
  sl_pg_source_store : SLRCrateId
  sl_wikimedia_candidate_provider : SLRCrateId
  sl_world_compiler : SLRCrateId
  sl_world_expansion_runtime : SLRCrateId
  sl_world_store : SLRCrateId
  sl_consumer_residual : SLRCrateId
  sl_proof_search_loop : SLRCrateId
  sl_proof_search_scheduler : SLRCrateId
  sl_residual_planner : SLRCrateId
  sl_route_executor : SLRCrateId
  sl_route_selector : SLRCrateId
  sl_semantic_admission : SLRCrateId
  sl_semantic_expansion : SLRCrateId
  sl_semantic_status : SLRCrateId
  sl_evidence_payment : SLRCrateId
  sl_evidential_reopen : SLRCrateId
  sl_expanded_cert : SLRCrateId
  sl_reviewed_evidence_payment : SLRCrateId
  sl_formal_proof_bridge : SLRCrateId
  sl_formal_proof_reopen : SLRCrateId
  sl_governed_legal_provider : SLRCrateId
  sl_legal_counterfactual : SLRCrateId
  sl_legal_follow_plan : SLRCrateId
  sl_legal_runtime : SLRCrateId
  sl_nsw_legislation_provider : SLRCrateId

record SLRCrateContract : Set where
  constructor crateContract
  field
    crateName : String
    layer : SLRCrateLayer
    inputCarrier : String
    outputCarrier : String
    createsSemanticTruth : Bool
    requiresReviewedOrKernelGate : Bool

slrCrateSpec : SLRCrateId → SLRCrateContract
slrCrateSpec sl_bench = crateContract "sl-bench" verificationAndCLI "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_cli = crateContract "sl-cli" verificationAndCLI "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_parity = crateContract "sl-parity" verificationAndCLI "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_core = crateContract "sl-core" coreCarrier "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_reader_model = crateContract "sl-reader-model" coreCarrier "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_stream = crateContract "sl-stream" coreCarrier "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_pg_source_store = crateContract "sl-pg-source-store" worldIngestionAndCompiler "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_wikimedia_candidate_provider = crateContract "sl-wikimedia-candidate-provider" worldIngestionAndCompiler "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_world_compiler = crateContract "sl-world-compiler" worldIngestionAndCompiler "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_world_expansion_runtime = crateContract "sl-world-expansion-runtime" worldIngestionAndCompiler "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_world_store = crateContract "sl-world-store" worldIngestionAndCompiler "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_consumer_residual = crateContract "sl-consumer-residual" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_proof_search_loop = crateContract "sl-proof-search-loop" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_proof_search_scheduler = crateContract "sl-proof-search-scheduler" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_residual_planner = crateContract "sl-residual-planner" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_route_executor = crateContract "sl-route-executor" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_route_selector = crateContract "sl-route-selector" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_semantic_admission = crateContract "sl-semantic-admission" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_semantic_expansion = crateContract "sl-semantic-expansion" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_semantic_status = crateContract "sl-semantic-status" residualAndRoutePlanning "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_evidence_payment = crateContract "sl-evidence-payment" evidenceReviewAndPayment "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_evidential_reopen = crateContract "sl-evidential-reopen" evidenceReviewAndPayment "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_expanded_cert = crateContract "sl-expanded-cert" evidenceReviewAndPayment "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_reviewed_evidence_payment = crateContract "sl-reviewed-evidence-payment" evidenceReviewAndPayment "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_formal_proof_bridge = crateContract "sl-formal-proof-bridge" formalProofAndReopen "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_formal_proof_reopen = crateContract "sl-formal-proof-reopen" formalProofAndReopen "source-scoped-input" "candidate-or-receipt" false true
slrCrateSpec sl_governed_legal_provider = crateContract "sl-governed-legal-provider" legalRuntimeAndProviders "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_legal_counterfactual = crateContract "sl-legal-counterfactual" legalRuntimeAndProviders "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_legal_follow_plan = crateContract "sl-legal-follow-plan" legalRuntimeAndProviders "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_legal_runtime = crateContract "sl-legal-runtime" legalRuntimeAndProviders "source-scoped-input" "candidate-or-receipt" false false
slrCrateSpec sl_nsw_legislation_provider = crateContract "sl-nsw-legislation-provider" legalRuntimeAndProviders "source-scoped-input" "candidate-or-receipt" false false

record CandidateDoesNotClaimTruth (c : SLRCrateContract) : Set where
  constructor candidateDoesNotClaimTruth
  field noTruthClaim : SLRCrateContract.createsSemanticTruth c ≡ false

all31CratesDoNotSelfCertifyTruth : (c : SLRCrateId) → CandidateDoesNotClaimTruth (slrCrateSpec c)
all31CratesDoNotSelfCertifyTruth sl_bench = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_cli = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_parity = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_core = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_reader_model = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_stream = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_pg_source_store = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_wikimedia_candidate_provider = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_world_compiler = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_world_expansion_runtime = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_world_store = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_consumer_residual = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_proof_search_loop = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_proof_search_scheduler = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_residual_planner = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_route_executor = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_route_selector = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_semantic_admission = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_semantic_expansion = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_semantic_status = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_evidence_payment = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_evidential_reopen = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_expanded_cert = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_reviewed_evidence_payment = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_formal_proof_bridge = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_formal_proof_reopen = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_governed_legal_provider = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_legal_counterfactual = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_legal_follow_plan = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_legal_runtime = candidateDoesNotClaimTruth refl
all31CratesDoNotSelfCertifyTruth sl_nsw_legislation_provider = candidateDoesNotClaimTruth refl
