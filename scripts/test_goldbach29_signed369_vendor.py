from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

PIN = ROOT / "vendor" / "meta-introspector-aok-goldbach29.VENDOR"
BRIDGE = ROOT / "DASHI" / "ComputerScience" / "Goldbach29Signed369VendorBridgeExact.agda"
MACRO = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29SuccessMacroExact.agda"
RECEIPT = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29ReductionReceiptExact.agda"
SEMANTICS = ROOT / "DASHI" / "ComputerScience" / "Goldbach29ExternalHaltingSemanticsExact.agda"
AUDIT30 = ROOT / "DASHI" / "ComputerScience" / "Goldbach30HaltingSourceAuditExact.agda"
HALTING = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29HaltingConsumerCompilerExact.agda"
SOTA = ROOT / "DASHI" / "ComputerScience" / "GoldbachMachineReductionSOTAExact.agda"
VIS = ROOT / "DASHI" / "ComputerScience" / "Goldbach30To29VisualizationConsumerExact.agda"
AGGREGATE = ROOT / "DASHI" / "EverythingGoldbach29Signed369VendorExact.agda"
WORKFLOW = ROOT / ".github" / "workflows" / "goldbach29-signed369-vendor.yml"


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


def test_bridge_reuses_signed369_and_descent_owners():
    text = BRIDGE.read_text()
    assert "SignedSSPFRACTRANWeaveExact" in text
    assert "FibreMachineFoundation369Exact" in text
    assert "ConsumerDescentMinimalObserverExact" in text
    assert "externalGoldbach29FractionCount" in text
    assert "externalGoldbach30FractionCount" in text
    assert "fineStateNeedNotEqualCoarseObserver" in text
    assert "goldbachReductionConsumerBoundary" in text


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
    assert "oldSuccessTerminal" in text
    assert "newSuccessTerminal" in text
    assert "successTerminalRegistersAgree" in text
    assert "successNextEvenConsumerPreserved" in text
    assert "successGoldbachVerdictConsumerPreserved" in text
    assert "newSuccessExecutionLengthIsOneMore" in text


def test_external_halting_semantics_is_cross_prover_only():
    text = SEMANTICS.read_text()
    assert "goldbachProg_halts_iff" in text
    assert "importedFormalTheoremSource" in text
    assert "externalGoldbach29HaltingSemanticsSourcePaid" in text
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


def test_halting_compiler_reduces_final_leaf_to_goldbach30_attachment():
    text = HALTING.read_text()
    assert "LogicalIff" in text
    assert "HaltingConsumerAttachment" in text
    assert "sameCounterexampleConsumerImpliesHaltingEquivalence" in text
    assert "goldbach29ExternalSourceCanFillRightHandRole" in text
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


def test_reduction_receipt_records_pareto_cut():
    text = RECEIPT.read_text()
    assert "Goldbach30To29ReductionReceipt" in text
    assert "commonRulePrefixCount" in text
    assert "fractionCountDeltaPaid" in text
    assert "controlStateDeltaPaid" in text
    assert "successConsumerPreservationPaid" in text
    assert "successExecutionPenaltyPaid" in text
    assert "externalGoldbach29HaltingSemanticsSourcePaidFlag" in text
    assert "wholeMachineReachableWeakBisimulationPaid" in text
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
    assert "Goldbach30To29SuccessMacroExact" in aggregate
    assert "Goldbach30To29ReductionReceiptExact" in aggregate
    assert "Goldbach29ExternalHaltingSemanticsExact" in aggregate
    assert "Goldbach30HaltingSourceAuditExact" in aggregate
    assert "Goldbach30To29HaltingConsumerCompilerExact" in aggregate
    assert "GoldbachMachineReductionSOTAExact" in aggregate
    assert "Goldbach30To29VisualizationConsumerExact" in aggregate
    assert "test_goldbach29_signed369_vendor.py" in workflow
    assert "EverythingGoldbach29Signed369VendorExact.agda" in workflow
