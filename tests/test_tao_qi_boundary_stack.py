from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def test_everything_imports_tao_qi_boundary_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Everything.agda").read_text(encoding="utf-8")

    required_imports = {
        "import DASHI.Culture.TaoChapterReadingReceipt",
        "import DASHI.Culture.TaoOperatorGrammar",
        "import DASHI.Interop.TaoQiReadingAdapter",
        "import DASHI.Interop.TaoMeditationQiAdapter",
        "import DASHI.Promotion.TaoQiObligationIndex",
    }

    for marker in required_imports:
        assert marker in text, marker


def test_promotion_index_references_tao_qi_boundary_surface() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "ObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "taoQiBoundaryLane" in text
    assert "import DASHI.Promotion.TaoQiObligationIndex as TaoQiBoundary" in text
    assert '"DASHI.Promotion.TaoQiObligationIndex"' in text
    assert '"canonicalTaoQiObligationIndexReceipt"' in text
    assert "crossDomainInterpretationBoundaryCount = 24" in text


def test_tao_qi_obligation_module_mentions_full_bridge_stack() -> None:
    text = (REPO_ROOT / "DASHI" / "Promotion" / "TaoQiObligationIndex.agda").read_text(
        encoding="utf-8"
    )

    assert "Tao / Qi obligation index" in text
    assert "candidate-only payload" in text or "candidate-only" in text
    assert "canonicalTaoSourceReceipt" in text
    assert "canonicalTaoOperatorGrammarReceipt" in text
    assert "canonicalQiOperatorTheoryBoundaryReceipt" in text
    assert "canonicalQiCarrierFieldBridgeReceipt" in text
    assert "canonicalTaoQiBridgeReceipt" in text
    assert "canonicalTaoMeditationQiBridgeReceipt" in text
