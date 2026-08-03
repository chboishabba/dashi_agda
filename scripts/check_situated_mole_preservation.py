#!/usr/bin/env python3
"""Static audit for the situated-mole, attribution, and disclosure tranche."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Core/AttributedSourceCore.agda": [
        "record AttributedSource",
        "citationImportsProofIsFalse",
        "citationCreatesAuthorityIsFalse",
        "record AttributedSourceAtlas",
        "attributedSourceAtlasReceipt",
    ],
    "DASHI/Culture/Preservation/ControlledDisclosureCore.agda": [
        "record FullArchive",
        "record ProjectionPolicy",
        "record PublicArtifact",
        "record PublicationReceipt",
        "publicViewDoesNotImplyCompleteRepresentation",
        "completeNonLeakageClaimIsFalse",
    ],
    "DASHI/Culture/Cuisine/CuisineKnowledgeSourceAtlas.agda": [
        "10.31644/ED.V8.N1.2021.A07",
        "10.36551/2081-1160.2019.24.75-100",
        "10.1093/9780190622138.003.0014",
        "10.1103/RevModPhys.95.025004",
        "canonicalCuisineKnowledgeSourceCountIsTwentyTwo",
    ],
    "DASHI/Culture/Cuisine/MoleProcessArchitecture.agda": [
        "fryThenRehydrateRoute",
        "rehydrateThenFryRoute",
        "canonicalAshRoute",
        "permanentSuspensionClaimIsFalse",
        "integratedDoesNotImplyErased",
    ],
    "DASHI/Culture/Cuisine/SituatedMoleWorld.agda": [
        "canonicalAfroMexicanMemoryBoundary",
        "Sweetgrass.sweetgrassAttribution",
        "Knot.canonicalKnotWeaveTopologyCultureBridge",
        "Hyper.canonicalHyperfabricIntersectionalBodyMemoryBridge",
        "noUniversalIndigenousMind",
        "completeInverseFromPlateClaimIsFalse",
    ],
    "DASHI/Culture/Cuisine/ControlledSuccessCore.agda": [
        "publicationDecision highPublicationRisk = abstainDecision",
        "publicationDecision unknownPublicationRisk = abstainDecision",
        "limitedProjectionDecision",
        "canonicalNoContactBoundary",
        "canonicalHuitlacocheRevalorisationCase",
    ],
    "DASHI/Culture/Cuisine/CuisineKnowledgeEcology.agda": [
        "candidateCuisineArchive",
        "candidateCuisineProjectionPolicy",
        "candidateCuisinePublicationReceipt",
        "archiveIsNotPublicViewClaimIsTrue",
    ],
    "DASHI/Culture/Cuisine/Everything.agda": [
        "DASHI.Core.AttributedSourceCore",
        "DASHI.Culture.Preservation.ControlledDisclosureCore",
        "DASHI.Culture.Cuisine.CuisineKnowledgeEcology",
    ],
    "DASHI/EverythingCuisineExtension.agda": [
        "import DASHI.Everything",
        "import DASHI.Culture.Cuisine.Everything",
    ],
    "scripts/build_public_projection.py": [
        "only the fail-closed default 'reject' is supported",
        "the attribution field cannot be silently removed",
        "claims_complete_non_leakage",
        "--self-test",
    ],
}


def main() -> int:
    failures: list[str] = []
    for relative_path, needles in REQUIRED.items():
        path = ROOT / relative_path
        if not path.exists():
            failures.append(f"missing file: {relative_path}")
            continue
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            if needle not in text:
                failures.append(f"{relative_path}: missing {needle!r}")

    if failures:
        print("situated-mole preservation audit failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print("situated-mole preservation audit passed")
    print(f"audited {len(REQUIRED)} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
