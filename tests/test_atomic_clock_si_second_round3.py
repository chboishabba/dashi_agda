from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI_ROOT = REPO_ROOT / "DASHI"
EVERYTHING = DASHI_ROOT / "Everything.agda"


@dataclass(frozen=True)
class ExpectedSurface:
    label: str
    filename_pattern: re.Pattern[str]
    required_names: tuple[str, ...]
    false_guards: tuple[str, ...]


ROUND3_SURFACES = (
    ExpectedSurface(
        label="SI-second authority artifact identity/evidence",
        filename_pattern=re.compile(
            r"(?:SISecond|Cs133|Metrology).*(?:Artifact|Authority|Evidence|Identity).*\.agda$"
        ),
        required_names=(
            "SISecondAuthorityArtifactIdentity",
            "canonicalSISecondAuthorityArtifactIdentity",
            "bipmNistCs133ArtifactEvidence",
            "artifactSHA256Evidence",
            "artifactAccessDateEvidence",
        ),
        false_guards=(
            "acceptedAuthorityArtifactPresent",
            "acceptedArtifactIdentityPresent",
            "authorityArtifactLoaded",
            "artifactEvidenceAccepted",
        ),
    ),
    ExpectedSurface(
        label="SI-second parsed exact carrier",
        filename_pattern=re.compile(
            r"(?:SISecond|Cs133|Metrology).*(?:Parsed|Parser|Carrier|Payload).*\.agda$"
        ),
        required_names=(
            "SISecondParsedExactCarrier",
            "canonicalSISecondParsedExactCarrier",
            "parsedExactCs133Integer",
            "parsedRawCs133Text",
            "zeroUncertaintyConvention",
        ),
        false_guards=(
            "parsedCarrierAccepted",
            "parsedPayloadPromoted",
            "numericPayloadPromoted",
            "carrierIngestedByConsumer",
        ),
    ),
    ExpectedSurface(
        label="atomic-clock covariance and independence receipt",
        filename_pattern=re.compile(
            r"(?:AtomicClock|SISecond|Metrology).*(?:Covariance|Independence|Receipt).*\.agda$"
        ),
        required_names=(
            "AtomicClockCovarianceIndependenceReceipt",
            "canonicalAtomicClockCovarianceIndependenceReceipt",
            "unitCovarianceLawRequested",
            "artifactIndependenceLawRequested",
            "consumerIndependenceReceiptRequired",
        ),
        false_guards=(
            "covarianceReceiptAccepted",
            "independenceReceiptAccepted",
            "consumerIngestionAccepted",
            "metrologyPromotionClaimed",
        ),
    ),
    ExpectedSurface(
        label="SI-second consumer ingestion receipt",
        filename_pattern=re.compile(
            r"(?:SISecond|AtomicClock|Metrology).*(?:Consumer|Ingestion|Adapter).*\.agda$"
        ),
        required_names=(
            "SISecondConsumerIngestionReceipt",
            "canonicalSISecondConsumerIngestionReceipt",
            "quantumClockConsumerIngestion",
            "stoneTimeParameterConsumerIngestion",
            "rydbergMetreConsumerIngestion",
        ),
        false_guards=(
            "consumerIngestionReceiptAccepted",
            "quantumClockIngestionPromoted",
            "stoneIngestionPromoted",
            "rydbergIngestionPromoted",
        ),
    ),
    ExpectedSurface(
        label="constructorless Candidate256 calibration authority token",
        filename_pattern=re.compile(
            r"(?:Candidate256|AtomicClock|Metrology).*(?:Calibration|Authority|Token).*\.agda$"
        ),
        required_names=(
            "Candidate256CalibrationAuthorityTokenRequest",
            "canonicalCandidate256CalibrationAuthorityTokenRequest",
            "constructorlessCandidate256CalibrationAuthorityToken",
            "noLocalCandidate256CalibrationAuthorityTokenConstructor",
            "externalCalibrationAuthorityStillRequired",
        ),
        false_guards=(
            "candidate256CalibrationAuthorityTokenAccepted",
            "candidate256CalibrationAuthorityTokenConstructed",
            "candidate256PhysicalCalibrationPromoted",
            "w4PhysicalCalibrationPromoted",
        ),
    ),
)

FORBIDDEN_PROMOTION_PATTERNS = (
    r"\b\w*(?:Promoted|PromotionClaimed|ClaimPromoted|AuthorityAccepted|ArtifactAccepted)"
    r"\w*\s*=\s*true\b",
    r"\bconstructs(?:External|Candidate256|SISecond|Metrology)\w*\s*=\s*true\b",
    r"\blocal(?:External|Candidate256|SISecond|Metrology)\w*Constructed\s*=\s*true\b",
    r"\baccepted(?:External|Authority|Artifact|Calibration)\w*Present\s*=\s*true\b",
)


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def agda_files() -> list[Path]:
    return [
        path
        for path in DASHI_ROOT.rglob("*.agda")
        if "_build" not in path.parts and "MAlonzo" not in path.parts
    ]


def find_surface_file(surface: ExpectedSurface) -> Path:
    matches = [
        path
        for path in agda_files()
        if surface.filename_pattern.search(str(path.relative_to(DASHI_ROOT)))
        and any(name in read_text(path) for name in surface.required_names)
    ]
    assert matches, f"missing expected round-3 SI/metrology surface: {surface.label}"
    assert len(matches) == 1, (
        f"expected one round-3 SI/metrology surface for {surface.label}, found: "
        + ", ".join(str(path.relative_to(REPO_ROOT)) for path in matches)
    )
    return matches[0]


def expected_surface_files() -> dict[ExpectedSurface, Path]:
    return {surface: find_surface_file(surface) for surface in ROUND3_SURFACES}


def module_name_from_text(text: str, path: Path) -> str:
    match = re.search(r"^\s*module\s+([A-Za-z0-9_.]+)\s+where\s*$", text, re.MULTILINE)
    assert match, f"{path.relative_to(REPO_ROOT)} missing Agda module header"
    return match.group(1)


def import_lines(text: str, module_name: str) -> list[str]:
    return re.findall(
        r"^\s*import\s+" + re.escape(module_name) + r"(?:\s+as\s+\w+)?\s*$",
        text,
        flags=re.MULTILINE,
    )


def assignment_to_value(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    patterns = (
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf";\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*Is{'True' if value else 'False'}\s*:"
        rf"[\s\S]{{0,320}}\b{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*\s*:[\s\S]{{0,320}}\b{expected}\b",
    )
    return any(re.search(pattern, text) for pattern in patterns)


def assert_any_false_guard(text: str, names: tuple[str, ...], label: str) -> None:
    assert any(assignment_to_value(text, name, False) for name in names), (
        f"{label} missing fail-closed false guard; expected one of: "
        + ", ".join(names)
    )
    promoted = [name for name in names if assignment_to_value(text, name, True)]
    assert promoted == [], f"{label} unexpectedly flips a guard true: {promoted}"


def test_round_three_si_metrology_expected_surface_files_exist_once() -> None:
    files = expected_surface_files()

    assert len(set(files.values())) == len(ROUND3_SURFACES), (
        "round-3 SI/metrology surfaces must be distinct files, found reuse across: "
        + ", ".join(str(path.relative_to(REPO_ROOT)) for path in files.values())
    )


def test_round_three_si_metrology_key_record_and_constant_names_appear() -> None:
    for surface, path in expected_surface_files().items():
        text = read_text(path)
        missing = [name for name in surface.required_names if name not in text]
        assert missing == [], (
            f"{path.relative_to(REPO_ROOT)} omits required {surface.label} names: "
            + ", ".join(missing)
        )

    combined = "\n".join(read_text(path) for path in expected_surface_files().values())
    for exact in (
        "9 192 631 770",
        "9192631770",
        "SHA256",
        "access-date",
        "BIPM",
        "NIST",
        "Delta nu Cs",
        "Candidate256",
    ):
        assert exact in combined, f"missing round-3 SI/metrology contact string: {exact}"


def test_round_three_si_metrology_fail_closed_booleans_remain_false() -> None:
    for surface, path in expected_surface_files().items():
        text = read_text(path)
        assert_any_false_guard(text, surface.false_guards, surface.label)

        for pattern in FORBIDDEN_PROMOTION_PATTERNS:
            assert not re.search(pattern, text), (
                f"{path.relative_to(REPO_ROOT)} contains forbidden promotion pattern: "
                + pattern
            )


def test_round_three_si_metrology_modules_are_imported_by_everything_once_integrated() -> None:
    everything = read_text(EVERYTHING)

    for path in expected_surface_files().values():
        module_name = module_name_from_text(read_text(path), path)
        imports = import_lines(everything, module_name)
        assert imports == [f"import {module_name}"], (
            "DASHI/Everything.agda must import exactly once after integration: "
            + module_name
        )
