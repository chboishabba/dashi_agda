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
  ingestion validation repair reporting governance artifactTransport candidateClosure residualGeometry : ToolKind

data AuthorityStatus : Set where
  bottom observed candidate diagnostic proposal receipt reviewed delegated promoted : AuthorityStatus

data ITIRMCPToolId : Set where
  itir_terminal_state : ITIRMCPToolId
  itir_terminal_picker : ITIRMCPToolId
  itir_terminal_observe : ITIRMCPToolId
  itir_chatgpt_pg_roster_list : ITIRMCPToolId
  itir_chatgpt_pg_roster_sync : ITIRMCPToolId
  itir_chatgpt_pg_hydrate_selected : ITIRMCPToolId
  itir_chatgpt_pg_hydrate_pending : ITIRMCPToolId
  itir_chatgpt_pg_search : ITIRMCPToolId
  itir_chatgpt_pg_read : ITIRMCPToolId
  itir_chatgpt_list_threads : ITIRMCPToolId
  itir_chatgpt_revive : ITIRMCPToolId
  itir_chatgpt_revive_multi : ITIRMCPToolId
  itir_chatgpt_session_status : ITIRMCPToolId
  itir_chatgpt_session_refresh_cffi : ITIRMCPToolId
  itir_chatgpt_session_refresh : ITIRMCPToolId
  itir_chatgpt_get_access_token : ITIRMCPToolId
  itir_chatgpt_cdp_capture : ITIRMCPToolId
  itir_chatgpt_hydrate : ITIRMCPToolId
  itir_chatgpt_operation_receipts : ITIRMCPToolId
  itir_chatgpt_dispatch_worker : ITIRMCPToolId
  itir_chatgpt_operation_status : ITIRMCPToolId
  itir_chatgpt_reconcile : ITIRMCPToolId
  itir_chatgpt_view_messages : ITIRMCPToolId
  itir_chatgpt_fleet_status : ITIRMCPToolId
  itir_chatgpt_fleet_opportunities : ITIRMCPToolId
  itir_chatgpt_tranche_status : ITIRMCPToolId
  itir_chatgpt_fleet_telemetry : ITIRMCPToolId
  itir_chatgpt_create_conversation : ITIRMCPToolId
  sensiblaw_itir_job_status : ITIRMCPToolId
  sensiblaw_obligations_query : ITIRMCPToolId
  sensiblaw_obligations_explain : ITIRMCPToolId
  sensiblaw_obligations_alignment : ITIRMCPToolId
  sensiblaw_obligations_projection : ITIRMCPToolId
  sensiblaw_obligations_activate : ITIRMCPToolId
  itir_compare_observations : ITIRMCPToolId
  itir_score_coherence : ITIRMCPToolId
  itir_build_envelope : ITIRMCPToolId
  itir_docstore_status : ITIRMCPToolId
  itir_docstore_open_questions : ITIRMCPToolId
  itir_obsidian_vault_scan : ITIRMCPToolId
  itir_docstore_proposal_receipt : ITIRMCPToolId
  itir_markdown_render_projection : ITIRMCPToolId
  itir_markdown_write_projection : ITIRMCPToolId
  itir_docstore_config_plan : ITIRMCPToolId
  itir_formal_latex_bridge : ITIRMCPToolId
  itir_pnf_distill_prompt : ITIRMCPToolId
  itir_pnf_eigen_motifs : ITIRMCPToolId
  itir_pnf_residual_cases : ITIRMCPToolId
  itir_pnf_governed_handoff : ITIRMCPToolId
  itir_archive_thread_view : ITIRMCPToolId
  itir_pnf_work_packet : ITIRMCPToolId
  itir_pnf_context_index : ITIRMCPToolId
  itir_pnf_task_memory_preview : ITIRMCPToolId
  itir_pnf_observer_evidence : ITIRMCPToolId
  itir_pnf_multi_parent_handoff : ITIRMCPToolId
  itir_spectral_render_scatter : ITIRMCPToolId
  itir_spectral_render_heatmap : ITIRMCPToolId
  itir_spectral_visualize_corpus : ITIRMCPToolId
  itir_spectral_candidate_packet : ITIRMCPToolId
  itir_governance_tool_profiles : ITIRMCPToolId
  itir_governance_validate_tool_profile : ITIRMCPToolId
  itir_wikidata_tooling_profile : ITIRMCPToolId
  itir_wikiproject_tooling_profile : ITIRMCPToolId
  itir_wikidata_review_packet : ITIRMCPToolId
  itir_wikidata_object_review_bundle : ITIRMCPToolId
  itir_wikidata_migration_candidate : ITIRMCPToolId
  itir_wikidata_disjointness_report : ITIRMCPToolId
  itir_climate_claim_review : ITIRMCPToolId
  itir_gwb_follow_graph : ITIRMCPToolId
  itir_zelph_transport_boundary : ITIRMCPToolId
  itir_zelph_hf_manifest_contract : ITIRMCPToolId
  itir_zelph_pack_sources : ITIRMCPToolId
  itir_zelph_partial_closure : ITIRMCPToolId
  itir_shard_validate_artifact : ITIRMCPToolId
  itir_shard_route_selector : ITIRMCPToolId
  itir_shard_partial_graph_view : ITIRMCPToolId
  itir_shard_bounded_graph_slice_plan : ITIRMCPToolId
  itir_shard_payload_probe : ITIRMCPToolId
  itir_formal_inspect : ITIRMCPToolId
  itir_formal_route : ITIRMCPToolId
  itir_formal_refine : ITIRMCPToolId
  itir_formal_certify : ITIRMCPToolId
  itir_ao_operation_review : ITIRMCPToolId
  itir_ao_operator_workflow : ITIRMCPToolId
  itir_ao_frontier_evidence : ITIRMCPToolId
  itir_ao_completed_operation_candidates : ITIRMCPToolId
  itir_ao_pareto_conductor : ITIRMCPToolId
  itir_ao_spawn_parallel_lanes : ITIRMCPToolId
  itir_ao_status : ITIRMCPToolId
  itir_ao_claim_lane : ITIRMCPToolId
  itir_ao_heartbeat : ITIRMCPToolId
  itir_ao_report_result : ITIRMCPToolId
  itir_ao_gap_check : ITIRMCPToolId

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
    canonicalBackingStore : String

-- All modeled outputs have authority 'observed', below 'receipt'.
-- No modeled tool claims promoted authority or self-promotion.
record ValidToolContract (c : MCPToolContract) : Set where
  constructor validContract
  field
    boundedOutput : MCPToolContract.maxOutputAuthority c ≡ receipt
    noUnreviewedMutation : MCPToolContract.mutates c ≡ false

toolSpec : ITIRMCPToolId → MCPToolContract
toolSpec itir_terminal_state = contract "itir_terminal_state" reporting true false observed receipt false "unverified-runtime-backing"
toolSpec itir_terminal_picker = contract "itir_terminal_picker" reporting true false observed receipt false "unverified-runtime-backing"
toolSpec itir_terminal_observe = contract "itir_terminal_observe" reporting true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_roster_list = contract "itir_chatgpt_pg_roster_list" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_roster_sync = contract "itir_chatgpt_pg_roster_sync" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_hydrate_selected = contract "itir_chatgpt_pg_hydrate_selected" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_hydrate_pending = contract "itir_chatgpt_pg_hydrate_pending" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_search = contract "itir_chatgpt_pg_search" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_pg_read = contract "itir_chatgpt_pg_read" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_list_threads = contract "itir_chatgpt_list_threads" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_revive = contract "itir_chatgpt_revive" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_revive_multi = contract "itir_chatgpt_revive_multi" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_session_status = contract "itir_chatgpt_session_status" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_session_refresh_cffi = contract "itir_chatgpt_session_refresh_cffi" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_session_refresh = contract "itir_chatgpt_session_refresh" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_get_access_token = contract "itir_chatgpt_get_access_token" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_cdp_capture = contract "itir_chatgpt_cdp_capture" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_hydrate = contract "itir_chatgpt_hydrate" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_operation_receipts = contract "itir_chatgpt_operation_receipts" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_dispatch_worker = contract "itir_chatgpt_dispatch_worker" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_operation_status = contract "itir_chatgpt_operation_status" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_reconcile = contract "itir_chatgpt_reconcile" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_view_messages = contract "itir_chatgpt_view_messages" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_fleet_status = contract "itir_chatgpt_fleet_status" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_fleet_opportunities = contract "itir_chatgpt_fleet_opportunities" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_tranche_status = contract "itir_chatgpt_tranche_status" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_fleet_telemetry = contract "itir_chatgpt_fleet_telemetry" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_chatgpt_create_conversation = contract "itir_chatgpt_create_conversation" governance true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_itir_job_status = contract "sensiblaw_itir_job_status" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_obligations_query = contract "sensiblaw_obligations_query" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_obligations_explain = contract "sensiblaw_obligations_explain" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_obligations_alignment = contract "sensiblaw_obligations_alignment" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_obligations_projection = contract "sensiblaw_obligations_projection" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec sensiblaw_obligations_activate = contract "sensiblaw_obligations_activate" candidateClosure true false observed receipt false "unverified-runtime-backing"
toolSpec itir_compare_observations = contract "itir_compare_observations" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_score_coherence = contract "itir_score_coherence" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_build_envelope = contract "itir_build_envelope" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_docstore_status = contract "itir_docstore_status" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_docstore_open_questions = contract "itir_docstore_open_questions" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_obsidian_vault_scan = contract "itir_obsidian_vault_scan" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_docstore_proposal_receipt = contract "itir_docstore_proposal_receipt" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_markdown_render_projection = contract "itir_markdown_render_projection" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_markdown_write_projection = contract "itir_markdown_write_projection" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_docstore_config_plan = contract "itir_docstore_config_plan" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_formal_latex_bridge = contract "itir_formal_latex_bridge" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_distill_prompt = contract "itir_pnf_distill_prompt" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_eigen_motifs = contract "itir_pnf_eigen_motifs" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_residual_cases = contract "itir_pnf_residual_cases" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_governed_handoff = contract "itir_pnf_governed_handoff" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_archive_thread_view = contract "itir_archive_thread_view" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_work_packet = contract "itir_pnf_work_packet" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_context_index = contract "itir_pnf_context_index" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_task_memory_preview = contract "itir_pnf_task_memory_preview" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_observer_evidence = contract "itir_pnf_observer_evidence" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_pnf_multi_parent_handoff = contract "itir_pnf_multi_parent_handoff" ingestion true false observed receipt false "unverified-runtime-backing"
toolSpec itir_spectral_render_scatter = contract "itir_spectral_render_scatter" residualGeometry true false observed receipt false "unverified-runtime-backing"
toolSpec itir_spectral_render_heatmap = contract "itir_spectral_render_heatmap" residualGeometry true false observed receipt false "unverified-runtime-backing"
toolSpec itir_spectral_visualize_corpus = contract "itir_spectral_visualize_corpus" residualGeometry true false observed receipt false "unverified-runtime-backing"
toolSpec itir_spectral_candidate_packet = contract "itir_spectral_candidate_packet" residualGeometry true false observed receipt false "unverified-runtime-backing"
toolSpec itir_governance_tool_profiles = contract "itir_governance_tool_profiles" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_governance_validate_tool_profile = contract "itir_governance_validate_tool_profile" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikidata_tooling_profile = contract "itir_wikidata_tooling_profile" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikiproject_tooling_profile = contract "itir_wikiproject_tooling_profile" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikidata_review_packet = contract "itir_wikidata_review_packet" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikidata_object_review_bundle = contract "itir_wikidata_object_review_bundle" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikidata_migration_candidate = contract "itir_wikidata_migration_candidate" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_wikidata_disjointness_report = contract "itir_wikidata_disjointness_report" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_climate_claim_review = contract "itir_climate_claim_review" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_gwb_follow_graph = contract "itir_gwb_follow_graph" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_zelph_transport_boundary = contract "itir_zelph_transport_boundary" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_zelph_hf_manifest_contract = contract "itir_zelph_hf_manifest_contract" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_zelph_pack_sources = contract "itir_zelph_pack_sources" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_zelph_partial_closure = contract "itir_zelph_partial_closure" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_shard_validate_artifact = contract "itir_shard_validate_artifact" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_shard_route_selector = contract "itir_shard_route_selector" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_shard_partial_graph_view = contract "itir_shard_partial_graph_view" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_shard_bounded_graph_slice_plan = contract "itir_shard_bounded_graph_slice_plan" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_shard_payload_probe = contract "itir_shard_payload_probe" artifactTransport true false observed receipt false "unverified-runtime-backing"
toolSpec itir_formal_inspect = contract "itir_formal_inspect" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_formal_route = contract "itir_formal_route" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_formal_refine = contract "itir_formal_refine" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_formal_certify = contract "itir_formal_certify" validation true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_operation_review = contract "itir_ao_operation_review" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_operator_workflow = contract "itir_ao_operator_workflow" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_frontier_evidence = contract "itir_ao_frontier_evidence" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_completed_operation_candidates = contract "itir_ao_completed_operation_candidates" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_pareto_conductor = contract "itir_ao_pareto_conductor" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_spawn_parallel_lanes = contract "itir_ao_spawn_parallel_lanes" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_status = contract "itir_ao_status" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_claim_lane = contract "itir_ao_claim_lane" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_heartbeat = contract "itir_ao_heartbeat" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_report_result = contract "itir_ao_report_result" governance true false observed receipt false "unverified-runtime-backing"
toolSpec itir_ao_gap_check = contract "itir_ao_gap_check" governance true false observed receipt false "unverified-runtime-backing"

all93ToolsHaveValidAuthorityProfile : (t : ITIRMCPToolId) → ValidToolContract (toolSpec t)
all93ToolsHaveValidAuthorityProfile itir_terminal_state = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_terminal_picker = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_terminal_observe = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_roster_list = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_roster_sync = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_hydrate_selected = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_hydrate_pending = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_search = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_pg_read = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_list_threads = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_revive = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_revive_multi = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_session_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_session_refresh_cffi = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_session_refresh = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_get_access_token = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_cdp_capture = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_hydrate = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_operation_receipts = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_dispatch_worker = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_operation_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_reconcile = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_view_messages = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_fleet_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_fleet_opportunities = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_tranche_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_fleet_telemetry = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_chatgpt_create_conversation = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_itir_job_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_obligations_query = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_obligations_explain = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_obligations_alignment = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_obligations_projection = validContract refl refl
all93ToolsHaveValidAuthorityProfile sensiblaw_obligations_activate = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_compare_observations = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_score_coherence = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_build_envelope = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_docstore_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_docstore_open_questions = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_obsidian_vault_scan = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_docstore_proposal_receipt = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_markdown_render_projection = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_markdown_write_projection = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_docstore_config_plan = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_formal_latex_bridge = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_distill_prompt = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_eigen_motifs = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_residual_cases = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_governed_handoff = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_archive_thread_view = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_work_packet = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_context_index = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_task_memory_preview = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_observer_evidence = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_pnf_multi_parent_handoff = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_spectral_render_scatter = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_spectral_render_heatmap = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_spectral_visualize_corpus = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_spectral_candidate_packet = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_governance_tool_profiles = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_governance_validate_tool_profile = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikidata_tooling_profile = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikiproject_tooling_profile = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikidata_review_packet = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikidata_object_review_bundle = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikidata_migration_candidate = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_wikidata_disjointness_report = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_climate_claim_review = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_gwb_follow_graph = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_zelph_transport_boundary = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_zelph_hf_manifest_contract = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_zelph_pack_sources = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_zelph_partial_closure = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_shard_validate_artifact = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_shard_route_selector = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_shard_partial_graph_view = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_shard_bounded_graph_slice_plan = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_shard_payload_probe = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_formal_inspect = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_formal_route = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_formal_refine = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_formal_certify = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_operation_review = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_operator_workflow = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_frontier_evidence = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_completed_operation_candidates = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_pareto_conductor = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_spawn_parallel_lanes = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_status = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_claim_lane = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_heartbeat = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_report_result = validContract refl refl
all93ToolsHaveValidAuthorityProfile itir_ao_gap_check = validContract refl refl

data TransportMode : Set where
  headlessCFFI explicitBootstrapCDP : TransportMode

data RetryPolicy : Set where
  noUncertainCommitRetry readOnlyRetry : RetryPolicy

data ReGPTMCPFunctionId : Set where
  chatgpt_adapter_health : ReGPTMCPFunctionId
  chatgpt_adapter_health_reset : ReGPTMCPFunctionId
  chatgpt_branch : ReGPTMCPFunctionId
  chatgpt_continue : ReGPTMCPFunctionId
  chatgpt_edit_branch : ReGPTMCPFunctionId
  chatgpt_fleet_telemetry : ReGPTMCPFunctionId
  chatgpt_hydrate : ReGPTMCPFunctionId
  chatgpt_list : ReGPTMCPFunctionId
  chatgpt_live_activity : ReGPTMCPFunctionId
  chatgpt_live_status : ReGPTMCPFunctionId
  chatgpt_new : ReGPTMCPFunctionId
  chatgpt_operation_status : ReGPTMCPFunctionId
  chatgpt_protocol_compare : ReGPTMCPFunctionId
  chatgpt_protocol_fingerprint : ReGPTMCPFunctionId
  chatgpt_reconcile : ReGPTMCPFunctionId
  chatgpt_regenerate : ReGPTMCPFunctionId
  chatgpt_revive : ReGPTMCPFunctionId
  chatgpt_revive_multi : ReGPTMCPFunctionId
  chatgpt_session_bootstrap : ReGPTMCPFunctionId
  chatgpt_session_doctor : ReGPTMCPFunctionId
  chatgpt_session_refresh : ReGPTMCPFunctionId
  chatgpt_session_refresh_cffi : ReGPTMCPFunctionId
  chatgpt_session_status : ReGPTMCPFunctionId
  chatgpt_sync_roster : ReGPTMCPFunctionId
  chatgpt_tranche_status : ReGPTMCPFunctionId
  chatgpt_view : ReGPTMCPFunctionId

record ReGPTFunctionContract : Set where
  constructor regptContract
  field
    canonicalName : String
    transport : TransportMode
    readOnly : Bool
    retryPolicy : RetryPolicy

regptFunctionSpec : ReGPTMCPFunctionId → ReGPTFunctionContract
regptFunctionSpec chatgpt_adapter_health = regptContract "chatgpt_adapter_health" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_adapter_health_reset = regptContract "chatgpt_adapter_health_reset" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_branch = regptContract "chatgpt_branch" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_continue = regptContract "chatgpt_continue" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_edit_branch = regptContract "chatgpt_edit_branch" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_fleet_telemetry = regptContract "chatgpt_fleet_telemetry" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_hydrate = regptContract "chatgpt_hydrate" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_list = regptContract "chatgpt_list" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_live_activity = regptContract "chatgpt_live_activity" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_live_status = regptContract "chatgpt_live_status" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_new = regptContract "chatgpt_new" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_operation_status = regptContract "chatgpt_operation_status" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_protocol_compare = regptContract "chatgpt_protocol_compare" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_protocol_fingerprint = regptContract "chatgpt_protocol_fingerprint" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_reconcile = regptContract "chatgpt_reconcile" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_regenerate = regptContract "chatgpt_regenerate" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_revive = regptContract "chatgpt_revive" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_revive_multi = regptContract "chatgpt_revive_multi" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_session_bootstrap = regptContract "chatgpt_session_bootstrap" explicitBootstrapCDP false noUncertainCommitRetry
regptFunctionSpec chatgpt_session_doctor = regptContract "chatgpt_session_doctor" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_session_refresh = regptContract "chatgpt_session_refresh" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_session_refresh_cffi = regptContract "chatgpt_session_refresh_cffi" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_session_status = regptContract "chatgpt_session_status" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_sync_roster = regptContract "chatgpt_sync_roster" headlessCFFI false noUncertainCommitRetry
regptFunctionSpec chatgpt_tranche_status = regptContract "chatgpt_tranche_status" headlessCFFI true readOnlyRetry
regptFunctionSpec chatgpt_view = regptContract "chatgpt_view" headlessCFFI true readOnlyRetry
