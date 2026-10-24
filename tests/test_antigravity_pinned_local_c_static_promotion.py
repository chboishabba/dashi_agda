from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_pinned_local_c_terminal_producer_feeds_static_receipt_without_soft_r136_token():
    text = read("DASHI/Physics/Foundations/CMP119AntigravityPinnedLocalCTerminalToStaticExact.agda")
    for token in (
        "PinnedLocalCStaticAffineCalibration",
        "PinnedLocalCTerminalProducers",
        "pinnedLocalCVacuum",
        "compilePinnedLocalCToStaticReceipt",
        "softR136SameStateTokenRequiredOnTypedRoute",
    ):
        assert token in text
