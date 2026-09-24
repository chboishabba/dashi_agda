module DASHI.Interop.LeanRound11MachinReplayEvidenceExact where

------------------------------------------------------------------------
-- EXACT-HEAD LEAN ROUTE-B REPLAY EVIDENCE SNAPSHOT
--
-- Verification PR:
--   chboishabba/dashi_lean4#24
--
-- Verification branch:
--   agent/moonshine-round11-route-b-replay-20260924
--
-- Exact head at this snapshot:
--   1aeafa66a09285d13412a58199cd5c0ba6d99533
--
-- This module separates:
--
--   source implemented
--     from
--   execution observed.
--
-- The verifier, recursive import-closure walk, generated certificate compiler,
-- focused Lean kernel probe, focused axiom audit, and workflow are all written.
--
-- At this snapshot GitHub exposes no workflow run for the exact head, so no
-- exact-head kernel/Actions receipt is promoted here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record LeanRound11MachinReplayEvidence : Set where
  constructor lean-round11-machin-replay-evidence
  field
    repository : String
    pullRequest : String
    branch : String
    headSha : String

    verifierScript : String
    generatedCertificatePath : String
    focusedKernelProbe : String
    focusedAxiomAudit : String
    workflowPath : String

    contentAddressedBlobVerifierSourceOwned : Bool
    bishopSubmoduleCommitVerifierSourceOwned : Bool
    namedDeclarationVerifierSourceOwned : Bool
    recursiveAgdaImportClosureVerifierSourceOwned : Bool
    generatedLeanCertificateCompilerSourceOwned : Bool
    focusedKernelProbeSourceOwned : Bool
    focusedAxiomAuditSourceOwned : Bool
    focusedWorkflowSourceOwned : Bool

    exactHeadWorkflowRunObserved : Bool
    generatedCertificateKernelCheckedAtExactHead : Bool
    focusedProbeKernelCheckedAtExactHead : Bool
    focusedAxiomAuditObservedAtExactHead : Bool

    trustBoundary : String

open LeanRound11MachinReplayEvidence public

canonicalLeanRound11MachinReplayEvidence :
  LeanRound11MachinReplayEvidence
canonicalLeanRound11MachinReplayEvidence =
  lean-round11-machin-replay-evidence
    "chboishabba/dashi_lean4"
    "#24"
    "agent/moonshine-round11-route-b-replay-20260924"
    "1aeafa66a09285d13412a58199cd5c0ba6d99533"

    "scripts/verify_round11_machin_route_b.py"
    "Generated/BishopRound11MachinReplayCertificate.lean"
    "Integration/BishopRound11MachinReplayProbe.lean"
    "Integration/AxiomAuditMoonshineRound11RouteB.lean"
    ".github/workflows/moonshine-round11-route-b.yml"

    true true true true true true true true

    false false false false

    "The route-B mathematics is theorem-owned on Lean main and the exact provenance/kernel verification machinery is source-written on PR #24. No GitHub Actions run is visible for this exact head at this snapshot, and the current execution environment has no Lean/Lake executable. Therefore generated replay and exact-head kernel/axiom receipts remain unobserved rather than inferred."
