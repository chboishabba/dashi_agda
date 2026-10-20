from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def require(path: str, markers: list[str]) -> None:
    text = (ROOT / path).read_text(encoding="utf-8")
    for marker in markers:
        assert marker in text, f"missing {marker!r} in {path}"


def test_coreweave_microsoft_terminal_payer_boundary() -> None:
    require(
        "DASHI/Economics/AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact.agda",
        [
            "coreWeaveMicrosoftContract",
            "microsoftFY2026ExternalCash",
            "selectedNamedPayerExternalCashCapacity",
            "completeTerminalPayerProvenanceClosed",
            "contractPaymentsRealised",
            "circularRevenueEstablished",
        ],
    )


def test_final_reconciliation_imports_terminal_payer_cut() -> None:
    require(
        "DASHI/Economics/AIMaxCutReconciliation20261012FinalExact.agda",
        [
            "AICoreWeaveMicrosoftTerminalPayerBoundary20261012Exact",
            "coreWeaveNamedPayerCapacityPaid",
            "terminalPayerStillPartial",
        ],
    )
