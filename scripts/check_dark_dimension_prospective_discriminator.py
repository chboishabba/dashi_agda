from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionProspectiveDiscriminatorExact.agda": [
        "module DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact where",
        "fullShapeCosmologyAxis",
        "shortRangeGravityAxis",
        "jointProspectiveAxis",
        "sameCosmologyDifferentGravityWitness",
        "cosmologyCannotRecoverShortRangeGravity",
        "sameGravityDifferentCosmologyWitness",
        "shortRangeGravityCannotRecoverCosmology",
        "cosmologyRechartCannotRecoverShortRangeGravity",
        "cosmologyOnlyDoesNotPayUniqueMechanism",
        "shortRangeGravityOnlyDoesNotPayStringTheory",
        "jointAxisStillDoesNotPayStringTheory",
        "daoFutureFullShapeTarget",
        "darkDimensionMicronGravityTarget",
        "prospectivePacketStillOpen",
        "prospectivePacketDoesNotBecomeDASHIDerivedPrediction",
        "IntersectionalNonFactorability",
        "RequiredObserverAxisJoinAdequacyExact",
        "GRQuantumPredictionProtocol",
        "10.1103/y31p-9g5k",
        "10.1007/JHEP06(2024)047",
    ],
    "DASHI/Unified/DarkDimensionGRQuantumPromotionAdapterExact.agda": [
        "import DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact as Prospective",
        "prospectiveDiscriminatorDoesNotPayEmpiricalCompletion",
        "jointProspectiveAxisStillDoesNotPayStringTheory",
        "jointProspectiveAxisDoesNotPayTheoryOfEverything",
    ],
    "scripts/check_dark_dimension_string_promotion_boundary.py": [
        "DarkDimensionProspectiveDiscriminatorExact",
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Dark-dimension prospective discriminator static contract: OK")
