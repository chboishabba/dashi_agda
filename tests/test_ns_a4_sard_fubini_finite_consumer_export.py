from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
BOUNDARY = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSA4SardFubiniCompositeBoundary.agda"
)


def read_boundary() -> str:
    return BOUNDARY.read_text(encoding="utf-8")


def block_between(text: str, start: str, end: str) -> str:
    match = re.search(
        rf"{re.escape(start)}(?P<body>.*?){re.escape(end)}",
        text,
        flags=re.DOTALL,
    )
    assert match is not None, f"missing block from {start!r} to {end!r}"
    return match.group("body")


def bool_assignment(text: str, name: str, value: bool) -> bool:
    agda_value = "true" if value else "false"
    return (
        re.search(
            rf"^{re.escape(name)}\s*:\s*Bool\s*"
            rf"^{re.escape(name)}\s*=\s*"
            rf"^\s*{agda_value}\b",
            text,
            flags=re.DOTALL | re.MULTILINE,
        )
        is not None
    )


def test_composite_exports_and_consumes_finite_whitney_fubini_law() -> None:
    text = read_boundary()
    export_block = block_between(
        text,
        "data A4SardFubiniFiniteConsumerLawExport : Set where",
        "canonicalA4SardFubiniFiniteConsumerLawExport :",
    )
    canonical_export = block_between(
        text,
        "canonicalA4SardFubiniFiniteConsumerLawExport =",
        "data A4SardFubiniCompositeTarget : Set where",
    )

    assert "A4SardFubiniFiniteConsumerLawExport" in text
    assert "Fubini.FiniteWhitneyFubiniConsumerLaw" in export_block
    assert "Fubini.canonicalFiniteWhitneyFubiniConsumerLaw" in canonical_export
    assert "finiteConsumerLawExport :\n      A4SardFubiniFiniteConsumerLawExport" in text
    assert (
        "finiteConsumerLawExportIsCanonical :\n"
        "      finiteConsumerLawExport\n"
        "        ≡ canonicalA4SardFubiniFiniteConsumerLawExport"
    ) in text
    assert bool_assignment(
        text,
        "finiteWhitneyFubiniConsumerLawConsumedByA4Composite",
        True,
    )
    assert (
        "finiteConsumerLawConsumed :\n"
        "      finiteWhitneyFubiniConsumerLawConsumedByA4Composite ≡ true"
    ) in text
    assert "recordsFiniteWhitneyFubiniConsumerLawConsumption" in text


def test_composite_status_rows_keep_eighth_consumption_status() -> None:
    text = read_boundary()
    status_data = block_between(
        text,
        "data A4SardFubiniCompositeStatusRow : Set where",
        "canonicalA4SardFubiniCompositeStatusRows :",
    )
    canonical_status_rows = block_between(
        text,
        "canonicalA4SardFubiniCompositeStatusRows =",
        "A4SardFubiniCompositeStatusRowCount : Nat",
    )

    expected_rows = (
        "childBoundariesRecordedStatus",
        "finiteWhitneyFubiniConsumerLawExportedStatus",
        "dependencyChainRecordedStatus",
        "SardFubiniTheoremStillOpenStatus",
        "WhitneyCouplingStillOpenStatus",
        "A4OutputSupportTransferStillOpenStatus",
        "A6LeakageStillOpenStatus",
        "ClayAndTerminalPromotionHeldStatus",
    )
    for row in expected_rows:
        assert row in status_data, row
        assert row in canonical_status_rows, row

    assert canonical_status_rows.count("∷") == 8
    assert "A4SardFubiniCompositeStatusRowCountIs8" in text
    assert "A4SardFubiniCompositeStatusRowCount ≡ 8" in text
    assert "statusRowCount :\n      A4SardFubiniCompositeStatusRowCount ≡ 8" in text


def test_composite_keeps_output_support_a4_a6_clay_and_terminal_false() -> None:
    text = read_boundary()
    receipt = block_between(
        text,
        "record NSA4SardFubiniCompositeBoundary : Set where",
        "canonicalNSA4SardFubiniCompositeBoundary :",
    )
    canonical_receipt = text.split("canonicalNSA4SardFubiniCompositeBoundary =", 1)[1]

    for term in (
        "importedFubiniOutputSupportConsumerStillFalse :\n"
        "      Fubini.outputSupportLowerBoundConsumed ≡ false",
        "A4WhitneyCouplingStillFalse :\n"
        "      A4WhitneyCouplingInequalityProved ≡ false",
        "A4FourierOutputCouplingStillFalse :\n"
        "      A4LeiRenTianFourierOutputCouplingProved ≡ false",
        "A4OutputSupportTransferStillFalse :\n"
        "      A4OutputSupportTransferProved ≡ false",
        "A6LeakageIdentityStillFalse :\n"
        "      triadicCompensatedLeakageIdentityProved ≡ false",
        "claySolvedStillFalse :\n"
        "      fullClayNSSolved ≡ false",
        "clayPromotionStillFalse :\n"
        "      clayNavierStokesPromoted ≡ false",
        "terminalPromotionStillFalse :\n"
        "      terminalPromotion ≡ false",
    ):
        assert term in receipt, term

    for field in (
        "importedFubiniOutputSupportConsumerStillFalse",
        "A4WhitneyCouplingStillFalse",
        "A4FourierOutputCouplingStillFalse",
        "A4OutputSupportTransferStillFalse",
        "A6LeakageIdentityStillFalse",
        "claySolvedStillFalse",
        "clayPromotionStillFalse",
        "terminalPromotionStillFalse",
    ):
        assert re.search(rf";\s*{field}\s*=\s*refl\b", canonical_receipt), field

    for name in (
        "SardFubiniCompositeTheoremProved",
        "A4WhitneyCouplingInequalityProved",
        "A4LeiRenTianFourierOutputCouplingProved",
        "A4OutputSupportTransferProved",
        "triadicCompensatedLeakageIdentityProved",
        "fullClayNSSolved",
        "clayNavierStokesPromoted",
        "terminalPromotion",
    ):
        assert bool_assignment(text, name, False), name

    assert "Fubini.outputSupportLowerBoundConsumed ≡ false" in text
