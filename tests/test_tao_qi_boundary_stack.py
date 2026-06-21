from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def test_everything_imports_tao_qi_boundary_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Everything.agda").read_text(encoding="utf-8")

    required_imports = {
        "import DASHI.Culture.TaoChapterReadingReceipt",
        "import DASHI.Culture.TaoOperatorGrammar",
        "import DASHI.Culture.YinYangPolarityBoundary",
        "import DASHI.Interop.TaoYinYangAdapter",
        "import DASHI.Interop.YinYangQiAdapter",
        "import DASHI.Interop.PolarityPhaseFieldBridge",
        "import DASHI.Interop.TaoQiReadingAdapter",
        "import DASHI.Interop.TaoMeditationQiAdapter",
        "import DASHI.Promotion.PolarityFieldObligationIndex",
        "import DASHI.Promotion.TaoQiObligationIndex",
    }

    for marker in required_imports:
        assert marker in text, marker


def test_promotion_index_references_tao_qi_boundary_surface() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "taoQiBoundaryLane" in text
    assert "polarityFieldBoundaryLane" in text
    assert (
        "import DASHI.Promotion.PolarityFieldObligationIndex as PolarityFieldBoundary"
        in text
    )
    assert "import DASHI.Promotion.TaoQiObligationIndex as TaoQiBoundary" in text
    assert '"DASHI.Promotion.PolarityFieldObligationIndex"' in text
    assert '"canonicalPolarityFieldObligationIndexReceipt"' in text
    assert '"DASHI.Promotion.TaoQiObligationIndex"' in text
    assert '"canonicalTaoQiObligationIndexReceipt"' in text
    assert "crossDomainInterpretationBoundaryCount = 25" in text


def test_tao_qi_obligation_module_mentions_full_bridge_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "TaoQiObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "Tao / Qi obligation index" in text
    assert "candidate-only payload" in text or "candidate-only" in text
    assert "canonicalTaoSourceReceipt" in text
    assert "canonicalTaoOperatorGrammarReceipt" in text
    assert "canonicalYinYangPolarityBoundaryReceipt" in text
    assert "canonicalTaoYinYangBridgeReceipt" in text
    assert "canonicalYinYangQiBridgeReceipt" in text
    assert "canonicalPolarityPhaseFieldBridge" in text
    assert "canonicalQiOperatorTheoryBoundaryReceipt" in text
    assert "canonicalQiCarrierFieldBridgeReceipt" in text
    assert "canonicalTaoQiBridgeReceipt" in text
    assert "canonicalTaoMeditationQiBridgeReceipt" in text
    assert "canonicalPolarityFieldObligationIndexReceipt" in text


def test_tao_source_receipt_mentions_external_lean_formalism() -> None:
    text = (REPO_ROOT / "DASHI" / "Culture" / "TaoChapterReadingReceipt.agda").read_text(
        encoding="utf-8"
    )

    assert "taoLeanPastebinUrl" in text
    assert "https://pastebin.xware.online/paste/20260621_131250_taoteching_lean" in text
    assert "canonicalTaoExternalFormalismSource" in text
    assert "canonicalTaoSourceProvenanceSurface" in text


def test_polarity_field_index_mentions_actual_middle_layer_modules() -> None:
    text = (
        REPO_ROOT / "DASHI" / "Promotion" / "PolarityFieldObligationIndex.agda"
    ).read_text(encoding="utf-8")

    assert "DASHI.Culture.YinYangPolarityBoundary" in text
    assert "DASHI.Interop.TaoYinYangAdapter" in text
    assert "DASHI.Interop.YinYangQiAdapter" in text
    assert "DASHI.Interop.PolarityPhaseFieldBridge" in text
    assert "canonicalPolarityFieldObligationIndexReceipt" in text
