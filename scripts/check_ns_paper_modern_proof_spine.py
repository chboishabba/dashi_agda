#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "Docs/papers/live/Paper1NavierStokesClayDraft.md"
INTERFACE = ROOT / "DASHI/Papers/NavierStokes/TheoremInterface.agda"
PROGRAM = ROOT / "DASHI/Papers/NavierStokes/FourLaneProofProgramExact.agda"
CONTROL = ROOT / "Docs/roadmaps/NSProofControl20260915.md"
ADDENDUM = ROOT / "Docs/papers/NSFourLanePublicationAddendum20260915.md"

REQUIRED_PAPER = [
    "NSTriadKNPeriodicClayEligibilityMaxCutRound642Exact",
    "C1",
    "C2",
    "C3",
    "C4",
    "C5",
    "C6",
    "C7",
    "two",
    "genuinely new nonlinear",
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
    "FourLaneProofProgramExact",
    "NSTriadKNPeriodicClayEligibilityMaxCutRound642Exact",
    "periodicClayMaxCutC1Closed",
    "periodicClayMaxCutC2StillProofBearing",
    "periodicClayMaxCutC3CompilerAvailable",
    "periodicClayMaxCutC4CompilerAvailable",
    "periodicClayMaxCutC5Proved",
    "periodicClayMaxCutC6ScalarFTCInstalled",
    "periodicClayMaxCutC7SimonClosed",
    "oldPDFB1B2B3B4Mandatory",
    "oldPDFB7DirectCovarianceEqualityMandatory",
    "CommutatorOnlySpacetimeBudget568",
    "directCompanionConstructed",
    "commutatorOnlySpacetimeProducerClosed",
    "directLeafACompilerConstructed",
    "directOffDiagonalConsumerConstructed",
    "sameOutputDebtPaymentClosed",
    "p3SeparationProducerClosed",
    "historicalAlternativeRoute",
    "clayTerminalPromotion",
    "periodicBProofProgressDoesNotPromoteWholeSpaceA",
    "wholeSpaceAProofProgressDoesNotPromotePeriodicB",
    "forcedCDDoesNotSettleUnforcedAB",
    "R500.round500IntegratedDirectCompanionWeldClosedModuloIntegrationAuthority",
    "R568.round568LiveCommutatorSpacetimeBudgetClosed",
    "R572.round572R503DirectBudgetCompilerClosedGivenReceipts",
    "R503.round503ExactR500ToR415CompilerClosed",
    "R211.round211ConcreteSameOutputResidualPaymentConstructed",
    "R214.round214ConstantShellBandAlonePaysGramDebt",
]

REQUIRED_PROGRAM = [
    "wholeSpaceA",
    "periodicB",
    "forcedWholeSpaceC",
    "forcedPeriodicD",
    "periodicBIsActiveConstruction",
    "wholeSpaceAIsIndependentObligation",
    "forcedCDIsVerificationAndProvenance",
    "periodicBProofProgressDoesNotPromoteWholeSpaceA",
    "wholeSpaceAProofProgressDoesNotPromotePeriodicB",
    "forcedCDDoesNotSettleUnforcedAB",
    "gramP3AttemptRetainedAsHistoricalProvenance",
    "gramP3AttemptAbandonedAsPrimaryRoute",
    "r571CenteredTaylorSixThreeR568IsPeriodicB",
]

REQUIRED_CONTROL = [
    "A — unforced whole-space",
    "B — unforced periodic",
    "C — forced whole-space breakdown",
    "D — forced periodic breakdown",
    "R571",
    "centered/Taylor",
    "six-three",
    "R568",
    "historical/provenance",
    "P3",
    "does not imply",
]

REQUIRED_ADDENDUM = [
    "Lane A",
    "Lane B",
    "Lane C",
    "Lane D",
    "unforced whole-space",
    "unforced periodic",
    "forced whole-space",
    "forced periodic",
    "R571",
    "centered/Taylor",
    "six-three",
    "R568",
    "many-to-one observable map",
    "MathematicalStatus",
    "StatementStatus",
    "CertificationStatus",
]

REQUIRED_FAIL_CLOSED_PROOFS = [
    "commutatorOnlySpacetimeProducerClosedIsFalse",
    "sameOutputDebtPaymentClosedIsFalse",
    "p3SeparationProducerClosedIsFalse",
    "clayTerminalPromotionIsFalse",
]

REQUIRED_CONSTRUCTED_PROOFS = [
    "directCompanionConstructedIsTrue",
    "directLeafACompilerConstructedIsTrue",
    "directOffDiagonalConsumerConstructedIsTrue",
    "historicalA1A9RetainedIsTrue",
]

FORBIDDEN_PRIMARY_PAPER_PHRASES = [
    "Its live frontiers are the quantitative `A1/A3`",
    "Lane B literal centered/Taylor realization     open",
    "Lane B old second-moment/six-three transplant open on modern carrier",
    "The current Clay-blocking frontier is also sharp. The coupled `A1/A3` problem",
]

FORBIDDEN_CONTROL_PHRASES = [
    "### A — active independent unforced proof search",
    "### B — deferred unforced periodic/global consumer",
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
    program = PROGRAM.read_text(encoding="utf-8")
    control = CONTROL.read_text(encoding="utf-8")
    addendum = ADDENDUM.read_text(encoding="utf-8")

    require_all(paper, REQUIRED_PAPER, "paper")
    require_all(interface, REQUIRED_INTERFACE, "interface")
    require_all(program, REQUIRED_PROGRAM, "four-lane programme")
    require_all(control, REQUIRED_CONTROL, "proof-control record")
    require_all(addendum, REQUIRED_ADDENDUM, "publication addendum")
    require_all(interface, REQUIRED_FAIL_CLOSED_PROOFS, "interface fail-closed proofs")
    require_all(interface, REQUIRED_CONSTRUCTED_PROOFS, "interface constructed proofs")

    appendix = historical_appendix(paper)
    primary = paper[: len(paper) - len(appendix)] if appendix else paper
    for phrase in FORBIDDEN_PRIMARY_PAPER_PHRASES:
        if phrase in primary:
            fail(f"stale A1-A9 primary-frontier phrase remains: {phrase!r}")

    for phrase in FORBIDDEN_CONTROL_PHRASES:
        if phrase in control:
            fail(f"stale A/B lane assignment remains: {phrase!r}")

    print("PASS: modern NS paper/four-lane proof-program source contract")


if __name__ == "__main__":
    main()
