from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
YM = ROOT / "DASHI/Physics/YangMills"

R409 = YM / "BalabanCMP116CanonicalSelectedTermReplayExact.agda"
R429 = YM / "BalabanCMP116CanonicalTraceEntropyBudgetExact.agda"
RECEIPT = YM / "BalabanCMP116ResidualContractionReceiptExact.agda"
CLAY = YM / "YangMillsCanonicalClayResidualExact.agda"


def _read_safe(path: Path) -> str:
    assert path.exists(), f"missing {path}"
    text = path.read_text(encoding="utf-8")
    imports = "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("open import", "import"))
    )
    assert "Round" not in imports
    assert "RealAnalysisAxioms" not in imports
    assert "{-# OPTIONS --safe #-}" in text
    assert "{!!}" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)
    assert "--allow-unsolved-metas" not in text
    assert "clayPromotion = true" not in text
    assert "clayYangMillsPromoted = true" not in text
    return text


def test_r409_uses_fixed_selected_source_term_and_proof_relation():
    text = _read_safe(R409)
    assert "(SelectedSource : Set)" in text
    assert "(selectedSource : SelectedSource)" in text
    assert "(SelectedTerm : Set)" in text
    assert "(selectedTerm : SelectedTerm)" in text
    assert "(SelectedTermBelongsToSource : SelectedSource → SelectedTerm → Set)" in text
    assert "(ProofBearingEquality : SelectedSource → SelectedTerm → Set)" in text
    assert "proofBearingEquality : ProofBearingEquality selectedSource selectedTerm" in text


def test_r409_attachment_predicate_and_selected_term_are_not_record_fields():
    text = _read_safe(R409)
    assert not re.search(r"(?m)^\s{4}SelectedTermBelongsToSource\s*:", text)
    assert not re.search(r"(?m)^\s{4}selectedTerm\s*:", text)
    assert not re.search(r"(?m)^\s{4}ProofBearingEquality\s*:", text)
    assert "selectedTermSourceAttachment" in text


def test_r409_receipts_are_separate_and_non_authoritative():
    text = _read_safe(R409)
    assert "sourceTranscriptionReceipt" in text
    assert "executionReplayReceipt" in text
    assert "executionReplayCreatesProofEquality = false" in text
    assert "sourceTranscriptionCreatesProofEquality = false" in text
    assert "10.1007/BF01239022" in text
    assert "DASHI EXTENSION" in text


def test_r429_uses_fixed_trace_source_compiler_and_predicates():
    text = _read_safe(R429)
    assert "(SelectedSource : Set)" in text
    assert "(selectedSource : SelectedSource)" in text
    assert "(TraceCarrier : Set)" in text
    assert "(selectedTrace : TraceCarrier)" in text
    assert "(ExactCompilerStructure : Set)" in text
    assert "(exactCompilerStructure : ExactCompilerStructure)" in text
    assert "(QuantitativeTraceEntropyBound : ExactCompilerStructure → TraceCarrier → Set)" in text
    assert "(SameObjectTraceAttachment : SelectedSource → TraceCarrier → Set)" in text


def test_r429_record_carries_bound_and_attachment_evidence_only():
    text = _read_safe(R429)
    assert "quantitativeTraceEntropyBound :" in text
    assert "QuantitativeTraceEntropyBound exactCompilerStructure selectedTrace" in text
    assert "sameObjectTraceAttachment :" in text
    assert "SameObjectTraceAttachment selectedSource selectedTrace" in text
    for field_name in (
        "QuantitativeTraceEntropyBound",
        "SameObjectTraceAttachment",
        "selectedTrace",
        "exactCompilerStructure",
    ):
        assert not re.search(rf"(?m)^\s{{4}}{field_name}\s*:", text)


def test_r429_preserves_compiler_vs_analytic_firewall_and_attribution():
    text = _read_safe(R429)
    assert "compilerStructurePaysAnalyticBound = false" in text
    assert "analyticBoundPaysSourceAttachment = false" in text
    assert "10.1007/BF01239022" in text
    assert "DASHI EXTENSION" in text


def test_cmp116_receipt_records_contracted_but_unpaid_boundaries():
    text = _read_safe(RECEIPT)
    assert "r409ReplayReceiptsAreProofAuthority = false" in text
    assert "r409SelectedProofEqualityStillRequired = true" in text
    assert "r429CompilerStructurePaysQuantitativeBound = false" in text
    assert "r429QuantitativeBoundStillRequired = true" in text
    assert "r429SameObjectTraceAttachmentStillRequired = true" in text
    assert "clayPromotion = false" in text


def test_clay_scheduler_threads_cmp116_fixed_parameters_and_stays_qualified():
    text = _read_safe(CLAY)
    for alias in ("CMP109", "TransferGap", "R409", "R429", "Gap", "Limit"):
        assert f" as {alias} using ()" in text
    assert "R409.CMP116CanonicalSelectedTermReplay" in text
    assert "R429.CMP116CanonicalTraceEntropyBudget" in text
    assert "SelectedCMP116Source" in text
    assert "selectedCMP116Source" in text
    assert "selectedCMP116Term" in text
    assert "selectedR429Trace" in text
    assert "clayYangMillsPromoted = false" in text
    assert "clayPromotion = false" in text
