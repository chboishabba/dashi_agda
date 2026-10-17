from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "DASHI/Physics/Closure/NSCanonicalB4PhysicalR440AnalyticInterfaceExact.agda"


def _read() -> str:
    return MODULE.read_text(encoding="utf-8")


def _imports(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("import ", "open import "))
    )


def _field_block(text: str) -> str:
    blocks = re.findall(r"(?ms)^\s*field\s*\n(.*?)(?=^\S|\Z)", text)
    return "\n".join(blocks)


def test_b4_analytic_owner_is_safe_round_free_and_total():
    text = _read()
    assert "{-# OPTIONS --safe #-}" in text
    assert "Round" not in _imports(text)
    assert "{!!}" not in text
    assert "--allow-unsolved-metas" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)
    assert "RealAnalysisAxioms" not in _imports(text)


def test_b4_exact_three_analytic_payments_are_explicit():
    text = _read()
    for name in [
        "signedPhysicalR440Payment",
        "thetaDNonnegative",
        "strictHalfMargin",
    ]:
        assert name in text
    assert "signedWork ≤ ((thetaD * coreMass) + (cD * localED))" in text
    assert "zero ≤ thetaD" in text
    assert "(half + thetaD) < one" in text


def test_b4_reference_objects_operations_orders_and_attachments_are_external_parameters():
    text = _read()
    fields = _field_block(text)
    forbidden_fields = [
        "SelectedPeriodicSource",
        "Scalar",
        "selectedSource",
        "signedWork",
        "coreMass",
        "localED",
        "thetaD",
        "cD",
        "zero",
        "half",
        "one",
        "_+_",
        "_*_",
        "_≤_",
        "_<_",
        "SignedWorkBelongsToSource",
        "CoreMassBelongsToSource",
        "LocalEDBelongsToSource",
        "signedWorkSourceAttachment",
        "coreMassSourceAttachment",
        "localEDSourceAttachment",
    ]
    for name in forbidden_fields:
        assert not re.search(rf"(?m)^\s*{re.escape(name)}\s*:", fields)

    for name in forbidden_fields:
        assert name in text


def test_b4_safe_bridge_requires_external_legacy_attachment_implication():
    text = _read()
    assert "canonicalB4PaymentResidualFromAnalytic" in text
    assert "analyticPaymentImpliesCanonicalPayment" in text
    assert "CanonicalB4PhysicalR440PaymentResidual" in text
    fields = _field_block(text)
    assert not re.search(r"(?m)^\s*analyticPaymentImpliesCanonicalPayment\s*:", fields)


def test_b4_interface_does_not_promote_clay_or_claim_payment_closed():
    text = _read()
    assert "clayPromotion = true" not in text
    assert "b4DefectR440PhysicalPaymentClosed = true" not in text
    assert "DASHI extension" in text
