#!/usr/bin/env python3
"""No-promotion audit for the Perelman / Bruhat-Tits analogue modules."""

from __future__ import annotations

import sys
from dataclasses import dataclass
from pathlib import Path


TARGET_FILES = (
    "DASHI/Physics/Closure/PerelmanBTGeometrizationAnalogueIndex.agda",
    "DASHI/Physics/Closure/PerelmanBTAnalogueImportSmoke.agda",
    "DASHI/Physics/Closure/PerelmanRicciFlowAndGeometrizationBoundaryReceipt.agda",
    "DASHI/Physics/Closure/BTBallVolumeArithmetic.agda",
    "DASHI/Physics/Closure/BTBallVolumeEntropyBoundary.agda",
    "DASHI/Physics/Closure/BTBoundaryCrossSectionRows.agda",
    "DASHI/Physics/Closure/BTCanonicalNeckAnalogue.agda",
    "DASHI/Physics/Closure/BTGaussianDiagonalInputRows.agda",
    "DASHI/Physics/Closure/BTGaussianReducedVolumeBoundary.agda",
    "DASHI/Physics/Closure/BTGaussianReducedVolumeSurface.agda",
    "DASHI/Physics/Closure/BTNeckDepthScaleArithmetic.agda",
    "DASHI/Physics/Closure/BTNeckSurgeryObligationComposite.agda",
    "DASHI/Physics/Closure/BTProductDiagonalGrowthArithmetic.agda",
    "DASHI/Physics/Closure/BTProductShellVsEnvelopeRows.agda",
    "DASHI/Physics/Closure/GeometryAnalogueClassification.agda",
    "DASHI/Physics/Closure/GeometryJSJAnalogueCrosswalk.agda",
    "DASHI/Physics/Closure/JSJAnaloguePieceClassification.agda",
    "DASHI/Physics/Closure/JSJBlockerNormalization.agda",
    "DASHI/Physics/Closure/SurgeryCanonicalNeighborhoodObligationLadder.agda",
    "DASHI/Physics/Closure/SurgeryCanonicalNeighborhoodObstruction.agda",
    "DASHI/Physics/Closure/SurgeryObligationBlockerNormalization.agda",
    "DASHI/Physics/Closure/PerelmanBTAnalogueDashboard.agda",
    "DASHI/Physics/Closure/PerelmanBTGeometrizationAnalogueSummary.agda",
    "DASHI/Physics/Closure/PerelmanBTLedgerExactCounts.agda",
    "DASHI/Physics/Closure/PerelmanBTNoPromotionAuditSurface.agda",
    "DASHI/Physics/Closure/PerelmanBTNoPromotionLaw.agda",
    "DASHI/Physics/Closure/PerelmanBTRoundFullImportSmoke.agda",
    "DASHI/Physics/Probes/PerelmanBTAnalogueImportProbe.agda",
    "DASHI/Physics/Probes/PerelmanBTAnaloguePromotionProbe.agda",
)

FORBIDDEN_TOKENS = (
    "ConvergesPointwise",
    "promotedSmoothSurgeryNeighborhood",
    "ClayClaimPromoted = true",
    "GeometrizationClaimPromoted = true",
)

REQUIRED_TOKENS = (
    "PerelmanBTGeometrizationAnalogueIndex",
    "No local btGaussianReducedVolume",
    "constructibleRowCountIs10",
    "smoothAuthorityBlockerCountIs9",
    "NoPromotionReason",
    "PerelmanBTGeometrizationAnalogueSummary",
    "BTGaussianDiagonalInputRow",
    "BTNeckSurgeryObligationComposite",
    "BTNeckDepthScaleRow",
    "BTProductShellVsEnvelopeRow",
    "JSJBlockerNormalizationLedger",
    "PerelmanBTNoPromotionAuditSurface",
    "PerelmanBTAnalogueImportProbe",
    "BTBoundaryCrossSectionRow",
    "SurgeryObligationBlockerRow",
    "PerelmanBTLedgerExactCounts",
    "PerelmanBTAnalogueDashboard",
    "PerelmanBTRoundFullImportSmoke",
)


@dataclass(frozen=True)
class Hit:
    relpath: str
    line: int
    token: str


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def read_targets(root: Path) -> tuple[dict[str, str], list[str]]:
    texts: dict[str, str] = {}
    missing: list[str] = []
    for relpath in TARGET_FILES:
        path = root / relpath
        try:
            texts[relpath] = path.read_text(encoding="utf-8", errors="replace")
        except FileNotFoundError:
            missing.append(relpath)
        except OSError as exc:
            missing.append(f"{relpath} ({exc})")
    return texts, missing


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def find_forbidden(texts: dict[str, str]) -> list[Hit]:
    hits: list[Hit] = []
    for relpath in sorted(texts):
        text = texts[relpath]
        for token in FORBIDDEN_TOKENS:
            start = 0
            while True:
                offset = text.find(token, start)
                if offset == -1:
                    break
                hits.append(Hit(relpath, line_number(text, offset), token))
                start = offset + len(token)
    return hits


def find_missing_required(texts: dict[str, str]) -> list[str]:
    combined = "\n".join(texts[relpath] for relpath in sorted(texts))
    return [token for token in REQUIRED_TOKENS if token not in combined]


def print_report(missing_files: list[str], forbidden_hits: list[Hit], missing_required: list[str]) -> None:
    passed = not missing_files and not forbidden_hits and not missing_required
    status = "PASS" if passed else "FAIL"
    print(f"perelman_bt_no_promotion_audit: {status}")
    print(f"targets: {len(TARGET_FILES)}")
    print(f"forbidden patterns: {len(FORBIDDEN_TOKENS)}")
    print(f"required patterns: {len(REQUIRED_TOKENS)}")

    if missing_files:
        print("missing/unreadable files:")
        for relpath in missing_files:
            print(f"  - {relpath}")

    if forbidden_hits:
        print("forbidden hits:")
        for hit in forbidden_hits:
            print(f"  - {hit.relpath}:{hit.line}: {hit.token}")

    if missing_required:
        print("missing required patterns:")
        for token in missing_required:
            print(f"  - {token}")

    if passed:
        print("safe patterns present; forbidden promotion patterns absent")


def main() -> int:
    root = repo_root()
    texts, missing_files = read_targets(root)
    forbidden_hits = find_forbidden(texts)
    missing_required = find_missing_required(texts)
    print_report(missing_files, forbidden_hits, missing_required)
    return 1 if missing_files or forbidden_hits or missing_required else 0


if __name__ == "__main__":
    sys.exit(main())
