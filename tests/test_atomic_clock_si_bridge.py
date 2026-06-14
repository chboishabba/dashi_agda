from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

EXPECTED_FILENAMES = (
    "AtomicClockSISecondCalibrationBridge.agda",
    "Cs133NumericAuthorityPayloadRequest.agda",
    "QuantumClockSIObservableBridge.agda",
    "StoneSISecondTimeParameterBridge.agda",
    "RydbergClockMetreBridge.agda",
)


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def find_module_file(filename: str) -> Path:
    matches = [
        path
        for path in (REPO_ROOT / "DASHI").rglob(filename)
        if "_build" not in path.parts and "MAlonzo" not in path.parts
    ]
    assert matches, f"missing expected bridge module: {filename}"
    assert len(matches) == 1, (
        f"expected one bridge module named {filename}, found: "
        + ", ".join(str(path.relative_to(REPO_ROOT)) for path in matches)
    )
    return matches[0]


def module_name_from_text(text: str, path: Path) -> str:
    match = re.search(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\s*$", text, re.MULTILINE)
    assert match, f"{path.relative_to(REPO_ROOT)} missing Agda module header"
    return match.group(1)


def expected_module_files() -> dict[str, Path]:
    return {filename: find_module_file(filename) for filename in EXPECTED_FILENAMES}


def normalize(text: object) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def assignment_to_value(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    patterns = [
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf";\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*Is{'True' if value else 'False'}\s*:\s*"
        rf"{re.escape(name)}\b[\s\S]*?\b{expected}\b",
    ]
    if not value:
        patterns.append(
            rf"\b{re.escape(name)}[A-Za-z0-9_']*\s*:\s*[\s\S]{{0,320}}\bfalse\b"
        )
    return any(re.search(pattern, text) for pattern in patterns)


def assert_any_flag_false(text: str, names: tuple[str, ...], label: str) -> None:
    assert any(assignment_to_value(text, name, False) for name in names), (
        f"{label} missing false guard; expected one of: " + ", ".join(names)
    )
    unexpected_true = [name for name in names if assignment_to_value(text, name, True)]
    assert unexpected_true == [], f"{label} promotes unexpectedly: {unexpected_true}"


def import_lines(text: str, module_name: str) -> list[str]:
    return re.findall(
        r"^\s*import\s+" + re.escape(module_name) + r"(?:\s+as\s+\w+)?\s*$",
        text,
        flags=re.MULTILINE,
    )


def assert_no_local_external_authority_construction(text: str, label: str) -> None:
    normalized = normalize(text)
    witness_variants = (
        "externalAuthorityLocallyConstructed",
        "locallyConstructedExternalAuthority",
        "localExternalAuthorityConstructed",
    )
    negative_witness_variants = (
        "noExternalAuthorityLocallyConstructed",
        "noLocalExternalAuthorityConstructor",
        "externalAuthorityNotLocallyConstructed",
    )
    textual_witness = (
        ("does not construct" in text or "not construct" in text)
        and ("AuthorityToken" in text or "external authority" in text.lower())
    )
    blocked_token_witness = (
        "UnavailableHere" in text
        or "Token →\n      ⊥" in text
        or "Token →\n  ⊥" in text
        or "promotionTokenBlocked" in text
        or "noLocal" in text
    )
    authority_present_false_witness = any(
        assignment_to_value(text, name, False)
        for name in (
            "acceptedAuthorityTokenPresent",
            "acceptedExternalAuthorityTokenPresent",
            "authorityArtifactPresent",
            "SISecondParameterSupplied",
            "hbarAuthorityPayloadSupplied",
        )
    )
    prose_authority_boundary = (
        ("does not load" in text and "authority" in text.lower())
        or ("no si-second authority token" in text.lower())
        or ("remain external" in text.lower() and "authority" in text.lower())
    )

    assert (
        any(assignment_to_value(text, name, False) for name in witness_variants)
        or any(assignment_to_value(text, name, True) for name in negative_witness_variants)
        or "no_external_authority_locally_constructed" in normalized
        or textual_witness
        or blocked_token_witness
        or authority_present_false_witness
        or prose_authority_boundary
    ), f"{label} missing explicit no-local-external-authority guard"

    forbidden_true_fragments = (
        "acceptedAuthorityTokenPresent",
        "acceptedExternalAuthorityTokenPresent",
        "externalAuthorityLocallyConstructed",
        "locallyConstructedExternalAuthority",
        "localExternalAuthorityConstructed",
    )
    for name in forbidden_true_fragments:
        assert not assignment_to_value(text, name, True), (
            f"{label} constructs or accepts local authority unexpectedly: {name}"
        )


def test_atomic_clock_si_expected_module_files_exist() -> None:
    for path in expected_module_files().values():
        assert path.is_file(), f"missing expected bridge module: {path.relative_to(REPO_ROOT)}"


def test_atomic_clock_si_modules_are_imported_by_everything_once_integrated() -> None:
    everything = read_text(EVERYTHING)

    for path in expected_module_files().values():
        module_name = module_name_from_text(read_text(path), path)
        imports = import_lines(everything, module_name)
        assert imports == [f"import {module_name}"], (
            "DASHI/Everything.agda must import exactly once after integration: "
            + module_name
        )


def test_atomic_clock_si_fail_closed_guards_remain_present() -> None:
    texts = {
        path.stem: read_text(path) for path in expected_module_files().values()
    }
    combined_text = "\n".join(texts.values())

    assert_any_flag_false(
        combined_text,
        ("acceptedAuthorityTokenPresent", "acceptedExternalAuthorityTokenPresent"),
        "atomic-clock/SI bridge lane",
    )
    assert_any_flag_false(
        combined_text,
        ("numericValuePromoted", "numericPayloadPromoted"),
        "atomic-clock/SI bridge lane",
    )
    assert_any_flag_false(
        combined_text,
        ("promotionClaimed", "promotesClaim", "siPromotionClaimed"),
        "atomic-clock/SI bridge lane",
    )
    assert_any_flag_false(
        combined_text,
        ("physicalStonePromotion", "stonePhysicalPromotion"),
        "Stone SI-second bridge",
    )
    assert_any_flag_false(
        combined_text,
        ("physicalHilbertColimit", "hilbertColimitPhysicalPromotion"),
        "quantum/Stone SI bridge",
    )
    assert_any_flag_false(
        combined_text,
        ("chemistryPromotion", "chemistryPromoted", "chemicalPromotionClaimed"),
        "Rydberg chemistry bridge",
    )

    for label, text in texts.items():
        assert_no_local_external_authority_construction(text, label)


def test_atomic_clock_si_empirical_contact_strings_are_exact() -> None:
    combined_text = "\n".join(read_text(path) for path in expected_module_files().values())

    for exact in (
        "9192631770",
        "9 192 631 770",
        "Delta phi = omega0 * Delta tau",
        "Hz",
        "R_infinity",
        "Rydberg formula",
    ):
        assert exact in combined_text, f"missing exact empirical contact string: {exact}"

    rydberg_formula_variants = (
        "1/lambda = R_infinity * (1/n1^2 - 1/n2^2)",
        "1 / lambda = R_infinity * (1 / n1^2 - 1 / n2^2)",
        "1 / lambda = R_infinity (1 / n_lower^2 - 1 / n_upper^2)",
        "nu = c * R_infinity * (1 / n1^2 - 1 / n2^2)",
        "E_n = - h c R_infinity / n^2",
    )
    compact_text = combined_text.replace(" ", "")
    assert any(variant in combined_text for variant in rydberg_formula_variants) or any(
        variant.replace(" ", "") in compact_text for variant in rydberg_formula_variants
    ), "missing Rydberg formula expression"
