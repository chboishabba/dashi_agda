from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI_ROOT = REPO_ROOT / "DASHI"

EXPECTED_FILENAMES = (
    "AtomicClockCandidate256DimensionAdapter.agda",
    "PlanckHbarSIPayloadRequest.agda",
    "SIDefiningConstantsAuthorityArtifactRequest.agda",
    "QuantumClockProperTimeRedshiftBridge.agda",
    "AtomicClockW4ReceiptAdapterRequest.agda",
)

RECEIPT_NAME = "Candidate256PhysicalCalibrationExternalReceipt"

W4_REQUIRED_RECEIPT_FIELDS = (
    "calibrationAuthority",
    "physicalUnitCarrier",
    "physicalDimensionVector",
    "natToUnitCalibrationMap",
    "calibratedQuotientScaleMap",
    "calibratedScaleMapFactorsThroughNat",
    "dimensionalPreservationLaw",
    "dimensionalPreservationAtWitness",
    "physicalUnitCarrierLabel",
    "physicalDimensionVectorLabel",
    "natToUnitCalibrationMapLabel",
    "calibratedQuotientScaleMapLabel",
    "factorizationLabel",
    "dimensionalPreservationLabel",
)


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def find_module_file(filename: str) -> Path:
    matches = [
        path
        for path in DASHI_ROOT.rglob(filename)
        if "_build" not in path.parts and "MAlonzo" not in path.parts
    ]
    assert matches, f"missing expected round-two SI module: {filename}"
    assert len(matches) == 1, (
        f"expected one module named {filename}, found: "
        + ", ".join(str(path.relative_to(REPO_ROOT)) for path in matches)
    )
    return matches[0]


def expected_module_files() -> dict[str, Path]:
    return {filename: find_module_file(filename) for filename in EXPECTED_FILENAMES}


def module_texts() -> dict[str, str]:
    return {
        filename: read_text(path)
        for filename, path in expected_module_files().items()
    }


def compact(text: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "", text).lower()


def assignment_to_value(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    patterns = (
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf";\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*Is{'True' if value else 'False'}\s*:"
        rf"[\s\S]{{0,260}}\b{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*\s*:[\s\S]{{0,260}}\b{expected}\b",
    )
    return any(re.search(pattern, text) for pattern in patterns)


def assert_any_false_guard(text: str, names: tuple[str, ...], label: str) -> None:
    assert any(assignment_to_value(text, name, False) for name in names), (
        f"{label} missing false guard; expected one of: " + ", ".join(names)
    )
    promoted = [name for name in names if assignment_to_value(text, name, True)]
    assert promoted == [], f"{label} unexpectedly promotes a false guard: {promoted}"


def test_round_two_si_expected_modules_exist_once() -> None:
    for filename, path in expected_module_files().items():
        assert path.name == filename
        assert path.is_file(), f"missing expected module: {filename}"


def test_round_two_si_modules_do_not_construct_external_receipts_locally() -> None:
    construction_patterns = (
        rf"\b\w+\s*:\s*(?:[A-Za-z0-9_.]+\.)?{RECEIPT_NAME}\b[\s\S]{{0,420}}\n"
        rf"\w+\s*=\s*record\b",
        rf"\bconstructs?{RECEIPT_NAME}\s*=\s*true\b",
        rf"\b\w+To{RECEIPT_NAME}\s*:",
        rf"\bcanonical{RECEIPT_NAME}\s*:",
    )

    for filename, text in module_texts().items():
        for pattern in construction_patterns:
            assert not re.search(pattern, text), (
                f"{filename} appears to construct {RECEIPT_NAME} locally"
            )

        lower = text.lower()
        assert (
            "does not construct candidate256physicalcalibrationexternalreceipt" in lower
            or "no candidate256physicalcalibrationexternalreceipt is constructed" in lower
            or assignment_to_value(text, f"constructs{RECEIPT_NAME}", False)
            or assignment_to_value(text, f"local{RECEIPT_NAME}Constructed", False)
            or "⊥" in text
        ), f"{filename} needs an explicit no-local-{RECEIPT_NAME} boundary"


def test_round_two_si_fail_closed_guards_remain_false() -> None:
    texts = module_texts()
    combined = "\n".join(texts.values())

    for filename, text in texts.items():
        assert re.search(r"\bfalse\b", text), f"{filename} has no explicit false guard"

    assert_any_false_guard(
        combined,
        (
            "authorityArtifactPresent",
            "authorityArtifactSupplied",
            "siDefiningConstantsAuthorityArtifactPresent",
            "siDefiningConstantsAuthorityArtifactSupplied",
            "acceptedExternalAuthorityTokenPresent",
        ),
        "SI defining constants authority request",
    )
    assert_any_false_guard(
        combined,
        (
            "hbarAuthorityPayloadSupplied",
            "hbarAuthorityArtifactPresent",
            "planckHbarPayloadSupplied",
            "hbarPayloadPromoted",
        ),
        "Planck hbar SI payload request",
    )
    assert_any_false_guard(
        combined,
        (
            "properTimeRedshiftPromoted",
            "redshiftLawPromoted",
            "grMetricAuthoritySupplied",
            "gravityConstantRequired",
        ),
        "proper-time redshift bridge",
    )
    assert_any_false_guard(
        combined,
        (
            "candidate256ReceiptConstructed",
            f"constructs{RECEIPT_NAME}",
            "w4ReceiptAdapterPromoted",
            "physicalCalibrationReceiptSupplied",
        ),
        "W4 receipt adapter request",
    )


def test_si_defining_constants_authority_request_names_exact_constants() -> None:
    text = module_texts()["SIDefiningConstantsAuthorityArtifactRequest.agda"]
    squashed = compact(text)

    exact_authority_strings = (
        "DASHI.Constants.Registry.canonicalSIDefiningConstants.Delta nu Cs",
        "DASHI.Constants.Registry.canonicalSIDefiningConstants.c",
        "DASHI.Constants.Registry.canonicalSIDefiningConstants.h",
    )
    for exact in exact_authority_strings:
        assert exact in text, f"missing exact SI authority request string: {exact}"

    assert "9192631770" in squashed, "missing exact Cs-133 SI-second value"
    assert "299792458" in squashed, "missing exact speed-of-light value"
    assert (
        "66260701510" in squashed
        or "6.62607015e-34" in text
        or "6.62607015 * 10^-34" in text
        or "6.62607015 x 10^-34" in text
    ), "missing exact Planck constant authority value"


def test_planck_hbar_payload_request_records_derived_si_hbar() -> None:
    text = module_texts()["PlanckHbarSIPayloadRequest.agda"]
    lower = text.lower()

    assert "hbar" in lower or "ℏ" in text, "hbar payload is not named"
    assert "derived" in lower, "hbar must be recorded as derived, not defining"
    assert (
        "h / (2 pi)" in text
        or "h/(2 pi)" in text
        or "h / 2pi" in text
        or "hbar = h / (2 pi)" in lower
        or "ℏ = h / (2π)" in text
        or "ℏ = h/(2π)" in text
    ), "missing hbar derivation from h and 2 pi"
    assert "J s" in text or "joule second" in lower or "joule-second" in lower
    assert (
        "DASHI.Constants.Registry.canonicalSIDefiningConstants.h" in text
    ), "hbar derivation must request the exact h authority source"


def test_quantum_clock_redshift_bridge_records_law_and_g_boundary() -> None:
    text = module_texts()["QuantumClockProperTimeRedshiftBridge.agda"]
    lower = text.lower()

    redshift_law_variants = (
        "Delta f / f = Delta U / c^2",
        "Delta nu / nu = Delta U / c^2",
        "Δf / f = ΔU / c^2",
        "Δν / ν = ΔU / c^2",
        "d tau = dt * sqrt(1 + 2 Phi / c^2)",
        "dτ = dt * sqrt(1 + 2 Φ / c^2)",
    )
    compact_text = compact(text)
    assert any(variant in text for variant in redshift_law_variants) or (
        "deltaf" in compact_text
        and "deltau" in compact_text
        and "c2" in compact_text
    ), "missing proper-time gravitational redshift law"

    assert (
        "Delta tau" in text
        or "Δτ" in text
        or "proper time" in lower
        or "proper-time" in lower
    ), "missing proper-time contact string"
    assert (
        "G not needed" in text
        or "G is not needed" in text
        or "does not require G" in text
        or "without Newtonian G" in text
        or "newtonian gravitational constant is not required" in lower
    ), "missing boundary that Newtonian G is not needed for the redshift law"
    assert "DASHI.Constants.Registry.canonicalSIDefiningConstants.c" in text


def test_atomic_clock_w4_adapter_request_names_required_receipt_fields() -> None:
    text = module_texts()["AtomicClockW4ReceiptAdapterRequest.agda"]

    assert RECEIPT_NAME in text, f"missing {RECEIPT_NAME} target"
    missing = [field for field in W4_REQUIRED_RECEIPT_FIELDS if field not in text]
    assert missing == [], "W4 adapter omits required receipt fields: " + ", ".join(missing)

    assert (
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation."
        "Candidate256PhysicalCalibrationExternalReceipt"
    ) in text, "W4 adapter must name the exact receipt module path"


def test_dimension_adapter_maps_time_frequency_angle_cycle_units() -> None:
    text = module_texts()["AtomicClockCandidate256DimensionAdapter.agda"]
    lower = text.lower()

    for token in ("second", "hertz", "radPerSecond", "cycle"):
        assert token in text, f"dimension adapter missing unit token: {token}"

    assert "s^-1" in text or "1/s" in text or "second^-1" in lower
    assert "dimensionless" in lower, "cycle/radian angle boundary should be dimensionless"
    assert (
        "radPerSecond" in text and ("hertz" in text or "Hz" in text)
    ), "dimension adapter must connect angular and cyclic frequency units"
