from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]

PIN = ROOT / "vendor" / "meta-introspector-aok-goldbach29.VENDOR"
VENDOR_ROOT = ROOT / "vendor" / "meta-introspector-aok"
VENDOR_LICENSE = VENDOR_ROOT / "LICENSE.AGPL-3.0"
VENDOR30 = VENDOR_ROOT / "c168223e96f7acc6179044f2a365a92db2e350c3" / "Goldbach30" / "Program.lean"
VENDOR29 = VENDOR_ROOT / "c168223e96f7acc6179044f2a365a92db2e350c3" / "Goldbach29" / "Program.lean"
VENDOR29_MAIN = VENDOR_ROOT / "428e2366045cb0b728115777df8bef14318a3bcf" / "Goldbach29" / "Main.lean"
VENDOR29_LOOPS = VENDOR_ROOT / "428e2366045cb0b728115777df8bef14318a3bcf" / "Goldbach29" / "Loops.lean"
VENDOR_NOTICE = VENDOR_ROOT / "NOTICE.md"
BRIDGE = ROOT / "DASHI" / "ComputerScience" / "Goldbach29Signed369VendorBridgeExact.agda"
SOURCE_ATTACH = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29VendoredSourceAttachmentExact.agda"
MACRO = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29SuccessMacroExact.agda"
TAIL = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29TailWeakSimulationExact.agda"
CHECKPOINT = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29CheckpointMachineExact.agda"
RECEIPT = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29ReductionReceiptExact.agda"
SEMANTICS = ROOT / "DASHI" / "ComputerScience" / "Goldbach29ExternalHaltingSemanticsExact.agda"
AUDIT30 = ROOT / "DASHI" / "ComputerScience" / "Goldbach30HaltingSourceAuditExact.agda"
HALTING = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29HaltingConsumerCompilerExact.agda"
SOTA = ROOT / "DASHI" / "ComputerScience" / "GoldbachMachineReductionSOTAExact.agda"
VIS = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29VisualizationConsumerExact.agda"
REPLAY = ROOT / "scripts" / "verify_goldbach30_29_replay.py"
AGGREGATE = ROOT / "DASHI" / "EverythingGoldbach29Signed369VendorExact.agda"
WORKFLOW = ROOT / ".github" / "workflows" / "goldbach29-signed369-vendor.yml"


def git_blob_sha(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def test_vendor_pin_and_attribution():
    text = PIN.read_text()
    assert "meta-introspector/aok" in text
    assert "c168223e96f7acc6179044f2a365a92db2e350c3" in text
    assert "d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Program.lean" in text
    assert "1fcb5ebe-bbab-4c12-bc38-4f1cd4739c1b/code/Cryptids/Goldbach30/Program.lean" in text
    assert "428e2366045cb0b728115777df8bef14318a3bcf" in text
    assert "d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Main.lean" in text
    assert "7added5000a75226a834ba7aab08a7380f0c70b3" in text
    assert "Goldbach30/Main.lean" in text
    assert "AGPL-3.0" in text
    assert "Goldbach29" in text and "Goldbach30" in text
    assert "fstep_enc" in text
    assert "goldbachProg_halts_iff" in text
    assert "Mike Dupont" in text or "meta-introspector" in text


def test_vendored_upstream_blobs_are_exact_and_licensed():
    assert VENDOR_LICENSE.exists()
    assert VENDOR_NOTICE.exists()
    assert git_blob_sha(VENDOR29) == "ff3f10a3e4c72771ac415a7f4bfb70a209478025"
    assert git_blob_sha(VENDOR30) == "ff748e1d68bf01d19e0c0998f6ac8d3a1c73e2f3"
    assert git_blob_sha(VENDOR29_MAIN) == "782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b"
    assert git_blob_sha(VENDOR29_LOOPS) == "782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b"
    assert VENDOR29_MAIN.read_bytes() == VENDOR29_LOOPS.read_bytes()
    notice = VENDOR_NOTICE.read_text()
    assert "Mike Dupont / meta-introspector" in notice
    assert "AGPL-3.0" in notice
    assert "Main.lean and Loops.lean are the same upstream blob" in notice
    license_notice = VENDOR_LICENSE.read_text()
    assert "0ad25db4bd1d86c452db3f9602ccdbe172438f52" in license_notice
    assert "does not claim to\nbe byte-identical" in license_notice


def test_bridge_reuses_signed369_and_descent_owners():
    text = BRIDGE.read_text()
    assert "SignedSSPFRACTRANWeaveExact" in text
    assert "FibreMachineFoundation369Exact" in text
    assert "ConsumerDescentMinimalObserverExact" in text
    assert "externalGoldbach29FractionCount" in text
    assert "externalGoldbach30FractionCount" in text
    assert "fineStateNeedNotEqualCoarseObserver" in text
    assert "goldbachReductionConsumerBoundary" in text


def test_source_attachment_is_byte_exact_but_proof_transport_fail_closed():
    text = SOURCE_ATTACH.read_text()
    assert "exactProgramSourceObjectsVendored = true" in text
    assert "sourceDrivenFractranReplayAvailable = true" in text
    assert "semanticMainLoopsDuplicateDetected = true" in text
    assert "semanticBuildAuthorityPaid = false" in text
    assert "crossProverProofTransportPaid = false" in text
    assert "concreteFractranCheckpointFormalAttachmentPaid = false" in text


def test_success_path_exposes_static_dynamic_tradeoff():
    text = BRIDGE.read_text()
    assert "oldSuccessExecutionLength" in text
    assert "newSuccessExecutionLength" in text
    assert "newSuccessExecutionLengthIsOneMore" in text
    assert "staticReductionCanIncreaseSuccessExecutionLength" in text
    assert "shortestProgramLengthEqualsExecutionLengthIsFalse" in text


def test_exact_success_macro_is_consumer_preserving():
    text = MACRO.read_text()
    assert "SuccessEntry" in text
    assert "aTail" in text
    assert "successEntryVerdictIsExactlyOne" in text
    assert "successEntryRestoreRegistersAreZero" in text
    assert "firstGoldbachSuccessEntry" in text
    assert "firstGoldbachSuccessOldTerminal" in text
    assert "firstGoldbachSuccessNewTerminal" in text
    assert "arbitraryPositiveVerdictClaimed" in text
    assert "arbitraryRestoreRegisterClaimed" in text
    assert "oldSuccessTerminal" in text
    assert "newSuccessTerminal" in text
    assert "successTerminalRegistersAgree" in text
    assert "successNextEvenConsumerPreserved" in text
    assert "successGoldbachVerdictConsumerPreserved" in text
    assert "reachableSuccessExecutionLengthIsOneMore" in text
    assert "fTail" not in text


def test_tail_weak_simulation_is_local_only():
    text = TAIL.read_text()
    assert "oldToNewPhase" in text
    assert "oldTransferPairMatchesNewTransferPair" in text
    assert "oldTerminalStepMatchesThreeNewSteps" in text
    assert "weakTailConsumerPreserved" in text
    assert "wholeMachineWeakBisimulationPaid = false" in text


def test_checkpoint_machine_proves_all_finite_consumer_traces_equal():
    text = CHECKPOINT.read_text()
    assert "SharedSearchKernel" in text
    assert "oldCheckpointStep" in text
    assert "newCheckpointStep" in text
    assert "checkpointStepAgree" in text
    assert "checkpointRunsAgree" in text
    assert "CheckpointHalts" in text
    assert "oldCheckpointHaltsIffNewCheckpointHalts" in text
    assert "sourceConcreteFractranAttachmentPaid = false" in text


def test_executable_replay_has_guard_checkpoint_and_source_regressions():
    text = REPLAY.read_text()
    assert "verify_macro_grid" in text
    assert "verify_checkpoint_replay" in text
    assert "arbitrary f>1" in text
    assert "s>0 selects restoration" in text
    assert "total29 - total30 == successes" in text
    assert "VENDOR29_PROGRAM" in text
    assert "VENDOR30_PROGRAM" in text
    assert "extract_fractran_program" in text
    assert "verify_vendored_fraction_programs" in text
    assert "verify_direct_fractran_step_bridge" in text


def test_external_halting_semantics_is_text_only_at_pinned_revision():
    text = SEMANTICS.read_text()
    assert "goldbachProg_halts_iff" in text
    assert "sourceVisibleTheoremText" in text
    assert "externalGoldbach29HaltingTheoremTextPresent = true" in text
    assert "externalGoldbach29MainLoopsSameBlob = true" in text
    assert "externalGoldbach29SemanticTreeBuildAuthorityPaid = false" in text
    assert "agdaGoldbach29HaltingSemanticsPaid = false" in text
    assert "goldbachConjectureProvedByUpstreamTheorem = false" in text


def test_goldbach30_commit_claim_is_not_promoted_without_source_file():
    text = AUDIT30.read_text()
    assert "7added5000a75226a834ba7aab08a7380f0c70b3" in text
    assert "goldbachProg_halts_iff" in text
    assert "developmentNarrativeClaim" in text
    assert "goldbach30NarrativeHaltingClaimFound = true" in text
    assert "goldbach30FormalHaltingSourceFound = false" in text
    assert "goldbach30MainFilePresentInAuditedTree = false" in text
    assert "goldbach30KnownMainPathHasCommitHistory = false" in text
    assert "goldbach30KnownLoopsPathHasCommitHistory = false" in text


def test_halting_compiler_requires_verified_external_authority():
    text = HALTING.read_text()
    assert "LogicalIff" in text
    assert "HaltingConsumerAttachment" in text
    assert "sameCounterexampleConsumerImpliesHaltingEquivalence" in text
    assert "goldbach29ExternalTheoremTextAvailable" in text
    assert "goldbach29ExternalSourceCanFillRightHandRole" in text
    assert "externalGoldbach29SemanticTreeBuildAuthorityPaid" in text
    assert "goldbach30HaltingAttachmentPaid = false" in text


def test_sota_attribution_keeps_deepmind_as_external_precedent():
    text = SOTA.read_text()
    assert "google-deepmind/cryptids" in text
    assert "f5d4559a82df052b2297be3349eccbf58b2c5a1d" in text
    assert "goldbach_25" in text and "goldbach_21" in text
    assert "339411" in text and "170966" in text
    assert "externalFormalReductionPrecedent" in text
    assert "deepMindResultProvesDashiFractranReduction = false" in text
    assert "staticCompressionCanIncreaseRuntimeHasIndependentPrecedent = true" in text


def test_reduction_receipt_records_separate_authority_currencies():
    text = RECEIPT.read_text()
    assert "Goldbach30To29ReductionReceipt" in text
    assert "commonRulePrefixCount" in text
    assert "fractionCountDeltaPaid" in text
    assert "controlStateDeltaPaid" in text
    assert "successConsumerPreservationPaid" in text
    assert "successExecutionPenaltyPaid" in text
    assert "exactProgramSourceObjectsVendoredFlag" in text
    assert "tailWeakSimulationPaidFlag" in text
    assert "sourceDrivenFractranReplayAvailableFlag" in text
    assert "externalGoldbach29SemanticBuildAuthorityPaidFlag" in text
    assert "crossProverProofTransportPaidFlag" in text
    assert "checkpointHaltingEquivalencePaidFlag" in text
    assert "sourceConcreteFractranAttachmentPaidFlag" in text
    assert "wholeMachineReachableWeakBisimulationPaid = false" in text


def test_visualization_consumer_uses_existing_observer_theory():
    text = VIS.read_text()
    assert "ConsumerDescentMinimalObserverExact" in text
    assert "FutureObservationalRefinement" in text
    assert "coarse369CannotDetermineExecutionLength" in text
    assert "consumerObserverRemainsLeastSufficient" in text


def test_no_unpaid_full_bisimulation_claim():
    text = BRIDGE.read_text()
    assert "fullReachableWeakBisimulationPaid" in text
    assert "fullReachableWeakBisimulationPaid = false" in text
    assert "mikeOwnsGoldbach29Construction" in text
    assert "dashiOwnsObserverTranslation" in text


def test_aggregate_and_workflow_own_the_new_surface():
    aggregate = AGGREGATE.read_text()
    workflow = WORKFLOW.read_text()
    assert "Goldbach29Signed369VendorBridgeExact" in aggregate
    assert "Goldbach30To29VendoredSourceAttachmentExact" in aggregate
    assert "Goldbach30To29SuccessMacroExact" in aggregate
    assert "Goldbach30To29TailWeakSimulationExact" in aggregate
    assert "Goldbach30To29CheckpointMachineExact" in aggregate
    assert "Goldbach30To29ReductionReceiptExact" in aggregate
    assert "Goldbach29ExternalHaltingSemanticsExact" in aggregate
    assert "Goldbach30HaltingSourceAuditExact" in aggregate
    assert "Goldbach30To29HaltingConsumerCompilerExact" in aggregate
    assert "GoldbachMachineReductionSOTAExact" in aggregate
    assert "Goldbach30To29VisualizationConsumerExact" in aggregate
    assert "vendor/meta-introspector-aok/**" in workflow
    assert "test_goldbach29_signed369_vendor.py" in workflow
    assert "test_goldbach_vendor_attachment.py" in workflow
    assert "verify_goldbach30_29_replay.py" in workflow
    assert "EverythingGoldbach29Signed369VendorExact.agda" in workflow
