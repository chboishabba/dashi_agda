from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_cerebras_cloud_margin_boundary() -> None:
    require(
        "DASHI/Economics/AICerebrasCloudMarginObserverBoundary20261012Exact.agda",
        [
            "q22026GaapCloudMarginIs1950bp",
            "q22026CoreCloudMarginIs4180bp",
            "gaapDirectionIsDown",
            "coreDirectionIsUp",
            "accountingGrossMarginPaid",
            "marginalInferenceServingMarginStillOpen",
        ],
    )
