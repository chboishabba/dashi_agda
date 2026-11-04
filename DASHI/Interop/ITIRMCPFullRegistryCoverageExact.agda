{-# OPTIONS --safe #-}
module DASHI.Interop.ITIRMCPFullRegistryCoverageExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

-- Finite manifest based on the supplied registry inventory.
-- Contract fields below are conservative specification defaults, not
-- extracted runtime profiles. Runtime correspondence remains unproved.
data ToolKind : Set where
  ingestion : ToolKind
  validation : ToolKind
  repair : ToolKind
  reporting : ToolKind
  governance : ToolKind
  artifactTransport : ToolKind
  candidateClosure : ToolKind
  residualGeometry : ToolKind

data AuthorityStatus : Set where
  bottom : AuthorityStatus
  observed : AuthorityStatus
  candidate : AuthorityStatus
  diagnostic : AuthorityStatus
  proposal : AuthorityStatus
  receipt : AuthorityStatus
  reviewed : AuthorityStatus
  delegated : AuthorityStatus
  promoted : AuthorityStatus

data BackingSubsystem : Set where
  pgChatArchiveStore : BackingSubsystem
  pgSensiblawObligationsStore : BackingSubsystem
  pgPNFSpectralStore : BackingSubsystem
  pgDocstoreVaultStore : BackingSubsystem
  pgAOCoordinatorStore : BackingSubsystem
  dashiAgdaPreflightIndex : BackingSubsystem
  zelphShardTransport : BackingSubsystem
  reGptHeadlessCurlCffi : BackingSubsystem
  itirTerminalObserver : BackingSubsystem

data ITIRMCPToolId : Set where
  itirTerminalState : ITIRMCPToolId
  itirTerminalPicker : ITIRMCPToolId
  itirTerminalObserve : ITIRMCPToolId
  itirChatgptPgRosterList : ITIRMCPToolId
  itirChatgptPgRosterSync : ITIRMCPToolId
  itirChatgptPgHydrateSelected : ITIRMCPToolId
  itirChatgptPgHydratePending : ITIRMCPToolId
  itirChatgptPgSearch : ITIRMCPToolId
  itirChatgptPgRead : ITIRMCPToolId
  itirChatgptListThreads : ITIRMCPToolId
  itirChatgptRevive : ITIRMCPToolId
  itirChatgptReviveMulti : ITIRMCPToolId
  itirChatgptSessionStatus : ITIRMCPToolId
  itirChatgptSessionRefreshCffi : ITIRMCPToolId
  itirChatgptSessionRefresh : ITIRMCPToolId
  itirChatgptGetAccessToken : ITIRMCPToolId
  itirChatgptCdpCapture : ITIRMCPToolId
  itirChatgptHydrate : ITIRMCPToolId
  itirChatgptOperationReceipts : ITIRMCPToolId
  itirChatgptDispatchWorker : ITIRMCPToolId
  itirChatgptOperationStatus : ITIRMCPToolId
  itirChatgptReconcile : ITIRMCPToolId
  itirChatgptViewMessages : ITIRMCPToolId
  itirChatgptFleetStatus : ITIRMCPToolId
  itirChatgptFleetOpportunities : ITIRMCPToolId
  itirChatgptTrancheStatus : ITIRMCPToolId
  itirChatgptFleetTelemetry : ITIRMCPToolId
  itirChatgptCreateConversation : ITIRMCPToolId
  sensiblawItirJobStatus : ITIRMCPToolId
  sensiblawObligationsQuery : ITIRMCPToolId
  sensiblawObligationsExplain : ITIRMCPToolId
  sensiblawObligationsAlignment : ITIRMCPToolId
  sensiblawObligationsProjection : ITIRMCPToolId
  sensiblawObligationsActivate : ITIRMCPToolId
  itirCompareObservations : ITIRMCPToolId
  itirScoreCoherence : ITIRMCPToolId
  itirBuildEnvelope : ITIRMCPToolId
  itirDocstoreStatus : ITIRMCPToolId
  itirDocstoreOpenQuestions : ITIRMCPToolId
  itirObsidianVaultScan : ITIRMCPToolId
  itirDocstoreProposalReceipt : ITIRMCPToolId
  itirMarkdownRenderProjection : ITIRMCPToolId
  itirMarkdownWriteProjection : ITIRMCPToolId
  itirDocstoreConfigPlan : ITIRMCPToolId
  itirFormalLatexBridge : ITIRMCPToolId
  itirPnfDistillPrompt : ITIRMCPToolId
  itirPnfEigenMotifs : ITIRMCPToolId
  itirPnfResidualCases : ITIRMCPToolId
  itirPnfGovernedHandoff : ITIRMCPToolId
  itirArchiveThreadView : ITIRMCPToolId
  itirPnfWorkPacket : ITIRMCPToolId
  itirPnfContextIndex : ITIRMCPToolId
  itirPnfTaskMemoryPreview : ITIRMCPToolId
  itirPnfObserverEvidence : ITIRMCPToolId
  itirPnfMultiParentHandoff : ITIRMCPToolId
  itirSpectralRenderScatter : ITIRMCPToolId
  itirSpectralRenderHeatmap : ITIRMCPToolId
  itirSpectralVisualizeCorpus : ITIRMCPToolId
  itirSpectralCandidatePacket : ITIRMCPToolId
  itirGovernanceToolProfiles : ITIRMCPToolId
  itirGovernanceValidateToolProfile : ITIRMCPToolId
  itirWikidataToolingProfile : ITIRMCPToolId
  itirWikiprojectToolingProfile : ITIRMCPToolId
  itirWikidataReviewPacket : ITIRMCPToolId
  itirWikidataObjectReviewBundle : ITIRMCPToolId
  itirWikidataMigrationCandidate : ITIRMCPToolId
  itirWikidataDisjointnessReport : ITIRMCPToolId
  itirClimateClaimReview : ITIRMCPToolId
  itirGwbFollowGraph : ITIRMCPToolId
  itirZelphTransportBoundary : ITIRMCPToolId
  itirZelphHfManifestContract : ITIRMCPToolId
  itirZelphPackSources : ITIRMCPToolId
  itirZelphPartialClosure : ITIRMCPToolId
  itirShardValidateArtifact : ITIRMCPToolId
  itirShardRouteSelector : ITIRMCPToolId
  itirShardPartialGraphView : ITIRMCPToolId
  itirShardBoundedGraphSlicePlan : ITIRMCPToolId
  itirShardPayloadProbe : ITIRMCPToolId
  itirFormalInspect : ITIRMCPToolId
  itirFormalRoute : ITIRMCPToolId
  itirFormalRefine : ITIRMCPToolId
  itirFormalCertify : ITIRMCPToolId
  itirAoOperationReview : ITIRMCPToolId
  itirAoOperatorWorkflow : ITIRMCPToolId
  itirAoFrontierEvidence : ITIRMCPToolId
  itirAoCompletedOperationCandidates : ITIRMCPToolId
  itirAoParetoConductor : ITIRMCPToolId
  itirAoSpawnParallelLanes : ITIRMCPToolId
  itirAoStatus : ITIRMCPToolId
  itirAoClaimLane : ITIRMCPToolId
  itirAoHeartbeat : ITIRMCPToolId
  itirAoReportResult : ITIRMCPToolId
  itirAoGapCheck : ITIRMCPToolId

record MCPToolContract : Set where
  constructor contract
  field
    canonicalName : String
    kind : ToolKind
    readOnly : Bool
    mutates : Bool
    inputAuthority : AuthorityStatus
    maxOutputAuthority : AuthorityStatus
    promotionRequiresGate : Bool
    hasExplicitAuthorityProfile : Bool
    backingSubsystem : BackingSubsystem

-- All modeled outputs have authority 'observed', below 'receipt'.
-- No modeled tool claims promoted authority or self-promotion.
record ValidToolContract (c : MCPToolContract) : Set where
  constructor validContract
  field
    noUnreviewedTruthPromotion : MCPToolContract.maxOutputAuthority c ≡ promoted → ⊥

toolSpec : ITIRMCPToolId → MCPToolContract
toolSpec itirTerminalState = contract "itir.terminal_state" reporting true false observed receipt false false itirTerminalObserver
toolSpec itirTerminalPicker = contract "itir.terminal_picker" reporting false true observed receipt true false itirTerminalObserver
toolSpec itirTerminalObserve = contract "itir.terminal_observe" reporting true false observed receipt false false itirTerminalObserver
toolSpec itirChatgptPgRosterList = contract "itir.chatgpt_pg_roster_list" ingestion true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptPgRosterSync = contract "itir.chatgpt_pg_roster_sync" ingestion false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptPgHydrateSelected = contract "itir.chatgpt_pg_hydrate_selected" ingestion false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptPgHydratePending = contract "itir.chatgpt_pg_hydrate_pending" ingestion false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptPgSearch = contract "itir.chatgpt_pg_search" ingestion true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptPgRead = contract "itir.chatgpt_pg_read" ingestion true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptListThreads = contract "itir.chatgpt_list_threads" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptRevive = contract "itir.chatgpt_revive" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptReviveMulti = contract "itir.chatgpt_revive_multi" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptSessionStatus = contract "itir.chatgpt_session_status" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptSessionRefreshCffi = contract "itir.chatgpt_session_refresh_cffi" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptSessionRefresh = contract "itir.chatgpt_session_refresh" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptGetAccessToken = contract "itir.chatgpt_get_access_token" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptCdpCapture = contract "itir.chatgpt_cdp_capture" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptHydrate = contract "itir.chatgpt_hydrate" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptOperationReceipts = contract "itir.chatgpt_operation_receipts" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptDispatchWorker = contract "itir.chatgpt_dispatch_worker" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptOperationStatus = contract "itir.chatgpt_operation_status" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptReconcile = contract "itir.chatgpt_reconcile" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec itirChatgptViewMessages = contract "itir.chatgpt_view_messages" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptFleetStatus = contract "itir.chatgpt_fleet_status" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptFleetOpportunities = contract "itir.chatgpt_fleet_opportunities" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptTrancheStatus = contract "itir.chatgpt_tranche_status" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptFleetTelemetry = contract "itir.chatgpt_fleet_telemetry" governance true false observed receipt false false reGptHeadlessCurlCffi
toolSpec itirChatgptCreateConversation = contract "itir.chatgpt_create_conversation" governance false true observed receipt true false reGptHeadlessCurlCffi
toolSpec sensiblawItirJobStatus = contract "sensiblaw.itir_job_status" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec sensiblawObligationsQuery = contract "sensiblaw.obligations_query" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec sensiblawObligationsExplain = contract "sensiblaw.obligations_explain" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec sensiblawObligationsAlignment = contract "sensiblaw.obligations_alignment" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec sensiblawObligationsProjection = contract "sensiblaw.obligations_projection" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec sensiblawObligationsActivate = contract "sensiblaw.obligations_activate" candidateClosure true false observed receipt false false pgSensiblawObligationsStore
toolSpec itirCompareObservations = contract "itir.compare_observations" validation true false observed receipt false false pgPNFSpectralStore
toolSpec itirScoreCoherence = contract "itir.score_coherence" validation true false observed receipt false false pgPNFSpectralStore
toolSpec itirBuildEnvelope = contract "itir.build_envelope" validation true false observed receipt false false pgPNFSpectralStore
toolSpec itirDocstoreStatus = contract "itir.docstore_status" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirDocstoreOpenQuestions = contract "itir.docstore_open_questions" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirObsidianVaultScan = contract "itir.obsidian_vault_scan" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirDocstoreProposalReceipt = contract "itir.docstore_proposal_receipt" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirMarkdownRenderProjection = contract "itir.markdown_render_projection" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirMarkdownWriteProjection = contract "itir.markdown_write_projection" artifactTransport false true observed receipt true false pgDocstoreVaultStore
toolSpec itirDocstoreConfigPlan = contract "itir.docstore_config_plan" artifactTransport true false observed receipt false false pgDocstoreVaultStore
toolSpec itirFormalLatexBridge = contract "itir.formal_latex_bridge" ingestion true false observed receipt false false dashiAgdaPreflightIndex
toolSpec itirPnfDistillPrompt = contract "itir.pnf_distill_prompt" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfEigenMotifs = contract "itir.pnf_eigen_motifs" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfResidualCases = contract "itir.pnf_residual_cases" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfGovernedHandoff = contract "itir.pnf_governed_handoff" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirArchiveThreadView = contract "itir.archive_thread_view" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfWorkPacket = contract "itir.pnf_work_packet" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfContextIndex = contract "itir.pnf_context_index" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfTaskMemoryPreview = contract "itir.pnf_task_memory_preview" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfObserverEvidence = contract "itir.pnf_observer_evidence" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirPnfMultiParentHandoff = contract "itir.pnf_multi_parent_handoff" ingestion true false observed receipt false false pgPNFSpectralStore
toolSpec itirSpectralRenderScatter = contract "itir.spectral_render_scatter" residualGeometry false true observed receipt true true pgPNFSpectralStore
toolSpec itirSpectralRenderHeatmap = contract "itir.spectral_render_heatmap" residualGeometry false true observed receipt true true pgPNFSpectralStore
toolSpec itirSpectralVisualizeCorpus = contract "itir.spectral_visualize_corpus" residualGeometry false true observed receipt true true pgPNFSpectralStore
toolSpec itirSpectralCandidatePacket = contract "itir.spectral_candidate_packet" residualGeometry true false observed receipt false true pgPNFSpectralStore
toolSpec itirGovernanceToolProfiles = contract "itir.governance_tool_profiles" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirGovernanceValidateToolProfile = contract "itir.governance_validate_tool_profile" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikidataToolingProfile = contract "itir.wikidata_tooling_profile" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikiprojectToolingProfile = contract "itir.wikiproject_tooling_profile" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikidataReviewPacket = contract "itir.wikidata_review_packet" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikidataObjectReviewBundle = contract "itir.wikidata_object_review_bundle" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikidataMigrationCandidate = contract "itir.wikidata_migration_candidate" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirWikidataDisjointnessReport = contract "itir.wikidata_disjointness_report" governance true false observed receipt false true pgPNFSpectralStore
toolSpec itirClimateClaimReview = contract "itir.climate_claim_review" governance true false observed receipt false false pgPNFSpectralStore
toolSpec itirGwbFollowGraph = contract "itir.gwb_follow_graph" governance true false observed receipt false false pgPNFSpectralStore
toolSpec itirZelphTransportBoundary = contract "itir.zelph_transport_boundary" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirZelphHfManifestContract = contract "itir.zelph_hf_manifest_contract" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirZelphPackSources = contract "itir.zelph_pack_sources" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirZelphPartialClosure = contract "itir.zelph_partial_closure" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirShardValidateArtifact = contract "itir.shard_validate_artifact" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirShardRouteSelector = contract "itir.shard_route_selector" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirShardPartialGraphView = contract "itir.shard_partial_graph_view" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirShardBoundedGraphSlicePlan = contract "itir.shard_bounded_graph_slice_plan" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirShardPayloadProbe = contract "itir.shard_payload_probe" artifactTransport true false observed receipt false true zelphShardTransport
toolSpec itirFormalInspect = contract "itir.formal_inspect" validation true false observed receipt false false dashiAgdaPreflightIndex
toolSpec itirFormalRoute = contract "itir.formal_route" validation true false observed receipt false false dashiAgdaPreflightIndex
toolSpec itirFormalRefine = contract "itir.formal_refine" validation true false observed receipt false false dashiAgdaPreflightIndex
toolSpec itirFormalCertify = contract "itir.formal_certify" validation true false observed receipt false false dashiAgdaPreflightIndex
toolSpec itirAoOperationReview = contract "itir.ao_operation_review" governance true false observed receipt false false pgAOCoordinatorStore
toolSpec itirAoOperatorWorkflow = contract "itir.ao_operator_workflow" governance true false observed receipt false false pgAOCoordinatorStore
toolSpec itirAoFrontierEvidence = contract "itir.ao_frontier_evidence" governance true false observed receipt false false pgAOCoordinatorStore
toolSpec itirAoCompletedOperationCandidates = contract "itir.ao_completed_operation_candidates" governance true false observed receipt false false pgAOCoordinatorStore
toolSpec itirAoParetoConductor = contract "itir.ao_pareto_conductor" governance false true observed receipt true false pgAOCoordinatorStore
toolSpec itirAoSpawnParallelLanes = contract "itir.ao_spawn_parallel_lanes" governance false true observed receipt true false pgAOCoordinatorStore
toolSpec itirAoStatus = contract "itir.ao_status" governance true false observed receipt false false pgAOCoordinatorStore
toolSpec itirAoClaimLane = contract "itir.ao_claim_lane" governance false true observed receipt true false pgAOCoordinatorStore
toolSpec itirAoHeartbeat = contract "itir.ao_heartbeat" governance false true observed receipt true false pgAOCoordinatorStore
toolSpec itirAoReportResult = contract "itir.ao_report_result" governance false true observed receipt true false pgAOCoordinatorStore
toolSpec itirAoGapCheck = contract "itir.ao_gap_check" governance true false observed receipt false false pgAOCoordinatorStore

all93ToolsHaveValidAuthorityProfile : (t : ITIRMCPToolId) → ValidToolContract (toolSpec t)
all93ToolsHaveValidAuthorityProfile itirTerminalState = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirTerminalPicker = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirTerminalObserve = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgRosterList = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgRosterSync = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgHydrateSelected = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgHydratePending = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgSearch = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptPgRead = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptListThreads = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptRevive = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptReviveMulti = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptSessionStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptSessionRefreshCffi = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptSessionRefresh = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptGetAccessToken = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptCdpCapture = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptHydrate = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptOperationReceipts = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptDispatchWorker = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptOperationStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptReconcile = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptViewMessages = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptFleetStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptFleetOpportunities = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptTrancheStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptFleetTelemetry = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirChatgptCreateConversation = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawItirJobStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawObligationsQuery = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawObligationsExplain = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawObligationsAlignment = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawObligationsProjection = validContract (λ ())
all93ToolsHaveValidAuthorityProfile sensiblawObligationsActivate = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirCompareObservations = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirScoreCoherence = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirBuildEnvelope = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirDocstoreStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirDocstoreOpenQuestions = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirObsidianVaultScan = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirDocstoreProposalReceipt = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirMarkdownRenderProjection = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirMarkdownWriteProjection = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirDocstoreConfigPlan = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirFormalLatexBridge = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfDistillPrompt = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfEigenMotifs = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfResidualCases = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfGovernedHandoff = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirArchiveThreadView = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfWorkPacket = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfContextIndex = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfTaskMemoryPreview = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfObserverEvidence = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirPnfMultiParentHandoff = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirSpectralRenderScatter = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirSpectralRenderHeatmap = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirSpectralVisualizeCorpus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirSpectralCandidatePacket = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirGovernanceToolProfiles = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirGovernanceValidateToolProfile = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikidataToolingProfile = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikiprojectToolingProfile = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikidataReviewPacket = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikidataObjectReviewBundle = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikidataMigrationCandidate = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirWikidataDisjointnessReport = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirClimateClaimReview = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirGwbFollowGraph = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirZelphTransportBoundary = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirZelphHfManifestContract = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirZelphPackSources = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirZelphPartialClosure = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirShardValidateArtifact = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirShardRouteSelector = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirShardPartialGraphView = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirShardBoundedGraphSlicePlan = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirShardPayloadProbe = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirFormalInspect = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirFormalRoute = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirFormalRefine = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirFormalCertify = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoOperationReview = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoOperatorWorkflow = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoFrontierEvidence = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoCompletedOperationCandidates = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoParetoConductor = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoSpawnParallelLanes = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoStatus = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoClaimLane = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoHeartbeat = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoReportResult = validContract (λ ())
all93ToolsHaveValidAuthorityProfile itirAoGapCheck = validContract (λ ())

data TransportMode : Set where
  headlessCFFI : TransportMode
  explicitBootstrapCDP : TransportMode

data RetryPolicy : Set where
  noUncertainCommitRetry : RetryPolicy
  readOnlyRetry : RetryPolicy

data ReGPTMCPFunctionId : Set where
  chatgptAdapterHealth : ReGPTMCPFunctionId
  chatgptAdapterHealthReset : ReGPTMCPFunctionId
  chatgptBranch : ReGPTMCPFunctionId
  chatgptContinue : ReGPTMCPFunctionId
  chatgptEditBranch : ReGPTMCPFunctionId
  chatgptFleetTelemetry : ReGPTMCPFunctionId
  chatgptHydrate : ReGPTMCPFunctionId
  chatgptList : ReGPTMCPFunctionId
  chatgptLiveActivity : ReGPTMCPFunctionId
  chatgptLiveStatus : ReGPTMCPFunctionId
  chatgptNew : ReGPTMCPFunctionId
  chatgptOperationStatus : ReGPTMCPFunctionId
  chatgptProtocolCompare : ReGPTMCPFunctionId
  chatgptProtocolFingerprint : ReGPTMCPFunctionId
  chatgptReconcile : ReGPTMCPFunctionId
  chatgptRegenerate : ReGPTMCPFunctionId
  chatgptRevive : ReGPTMCPFunctionId
  chatgptRevive_multi : ReGPTMCPFunctionId
  chatgptSessionBootstrap : ReGPTMCPFunctionId
  chatgptSessionDoctor : ReGPTMCPFunctionId
  chatgptSessionRefresh : ReGPTMCPFunctionId
  chatgptSessionRefreshCffi : ReGPTMCPFunctionId
  chatgptSessionStatus : ReGPTMCPFunctionId
  chatgptSyncRoster : ReGPTMCPFunctionId
  chatgptTrancheStatus : ReGPTMCPFunctionId
  chatgptView : ReGPTMCPFunctionId

record ReGPTFunctionContract : Set where
  constructor regptContract
  field
    canonicalName : String
    transport : TransportMode
    readOnly : Bool
    retryPolicy : RetryPolicy

regptFunctionSpec : ReGPTMCPFunctionId → ReGPTFunctionContract
regptFunctionSpec chatgptAdapterHealth = regptContract "chatgptAdapterHealth" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptAdapterHealthReset = regptContract "chatgptAdapterHealthReset" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptBranch = regptContract "chatgptBranch" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptContinue = regptContract "chatgptContinue" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptEditBranch = regptContract "chatgptEditBranch" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptFleetTelemetry = regptContract "chatgptFleetTelemetry" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptHydrate = regptContract "chatgptHydrate" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptList = regptContract "chatgptList" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptLiveActivity = regptContract "chatgptLiveActivity" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptLiveStatus = regptContract "chatgptLiveStatus" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptNew = regptContract "chatgptNew" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptOperationStatus = regptContract "chatgptOperationStatus" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptProtocolCompare = regptContract "chatgptProtocolCompare" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptProtocolFingerprint = regptContract "chatgptProtocolFingerprint" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptReconcile = regptContract "chatgptReconcile" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptRegenerate = regptContract "chatgptRegenerate" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptRevive = regptContract "chatgptRevive" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptRevive_multi = regptContract "chatgptRevive_multi" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptSessionBootstrap = regptContract "chatgptSessionBootstrap" explicitBootstrapCDP false noUncertainCommitRetry
regptFunctionSpec chatgptSessionDoctor = regptContract "chatgptSessionDoctor" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptSessionRefresh = regptContract "chatgptSessionRefresh" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptSessionRefreshCffi = regptContract "chatgptSessionRefreshCffi" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptSessionStatus = regptContract "chatgptSessionStatus" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptSyncRoster = regptContract "chatgptSyncRoster" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgptTrancheStatus = regptContract "chatgptTrancheStatus" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgptView = regptContract "chatgptView" headlessCFFI true readOnlyRetry
