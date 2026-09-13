#!/usr/bin/env python3
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "Docs/papers/live/Paper1NavierStokesClayDraft.md"
INTERFACE = ROOT / "DASHI/Papers/NavierStokes/TheoremInterface.agda"

REQUIRED_PAPER = [
    "CommutatorOnlySpacetimeBudget568",
    "R568",
    "R572",
    "R503",
    "C_direct",
    "same-output",
    "P3",
    "MathematicalStatus",
    "StatementStatus",
    "CertificationStatus",
    "historical/alternative",
    "A1-A9",
    "R214",
]

REQUIRED_INTERFACE = [
    "CommutatorOnlySpacetimeBudget568",
    "directCompanionConstructed",
    "commutatorOnlySpacetimeProducerClosed",
    "directLeafACompilerConstructed",
    "directOffDiagonalConsumerConstructed",
    "sameOutputDebtPaymentClosed",
    "p3SeparationProducerClosed",
    "historicalAlternativeRoute",
    "clayTerminalPromotion",
]

FORBIDDEN_PRIMARY_PAPER_PHRASES = [
    "Its live frontiers are the quantitative `A1/A3`",
    "The current Clay-blocking frontier is also sharp. The coupled `A1/A3` problem",
]


def fail(message: str) -> None:
    print(f"FAIL: {message}")
    raise SystemExit(1)


def require_all(text: str, needles: list[str], label: str) -> None:
    missing = [needle for needle in needles if needle not in text]
    if missing:
        fail(f"{label} missing required tokens: {missing}")


def historical_appendix(text: str) -> str:
    markers = [
        "## Historical/alternative A1-A9 route",
        "## Appendix: Historical/alternative A1-A9 route",
        "## Appendix A: Historical/alternative A1-A9 route",
    ]
    for marker in markers:
        if marker in text:
            return text.split(marker, 1)[1]
    return ""


def main() -> None:
    paper = PAPER.read_text(encoding="utf-8")
    interface = INTERFACE.read_text(encoding="utf-8")

    require_all(paper, REQUIRED_PAPER, "paper")
    require_all(interface, REQUIRED_INTERFACE, "interface")

    appendix = historical_appendix(paper)
    primary = paper[: len(paper) - len(appendix)] if appendix else paper
    for phrase in FORBIDDEN_PRIMARY_PAPER_PHRASES:
        if phrase in primary:
            fail(f"stale A1-A9 primary-frontier phrase remains: {phrase!r}")

    required_false_assignments = [
        "commutatorOnlySpacetimeProducerClosed = false",
        "sameOutputDebtPaymentClosed = false",
        "p3SeparationProducerClosed = false",
        "clayTerminalPromotion = false",
    ]
    for assignment in required_false_assignments:
        if assignment not in interface:
            fail(f"fail-closed interface assignment not found: {assignment}")

    required_true_assignments = [
        "directCompanionConstructed = true",
        "directLeafACompilerConstructed = true",
        "directOffDiagonalConsumerConstructed = true",
        "historicalA1A9Retained = true",
    ]
    for assignment in required_true_assignments:
        if assignment not in interface:
            fail(f"constructed/historical interface assignment not found: {assignment}")

    print("PASS: modern NS paper proof-spine source contract")


if __name__ == "__main__":
    main()
