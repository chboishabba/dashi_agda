from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionQuantitativeEnvelopeExact.agda": [
        "module DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact where",
        "darkDimensionRadiusLowerMicrometre",
        "darkDimensionRadiusUpperMicrometre",
        "darkDimensionRadiusEnvelope",
        "bedroyaCPrimeEnvelope",
        "daoPercentLevelAmplitudeBand",
        "sourceEnvelopeDoesNotEqualLockedPrediction",
        "qualitativeBandCannotManufactureExactAmplitude",
        "crossModelNumericalSeparationStillOpen",
        "prospectiveQuantitativeSeparationStillOpen",
        "DASHI.Physics.Units.SI",
        "DASHI.Empirical.GRQuantumPredictionProtocol",
        "10.1007/JHEP06(2024)047",
        "10.1103/1rsq-cv2m",
        "10.1103/y31p-9g5k",
    ],
    "DASHI/Empirical/DarkDimensionProspectiveDiscriminatorExact.agda": [
        "import DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact as Quantitative",
        "quantitativeEnvelopeStillDoesNotLockProspectivePacket",
    ],
    "scripts/check_dark_dimension_prospective_discriminator.py": [
        "DarkDimensionQuantitativeEnvelopeExact",
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

print("Dark-dimension quantitative-envelope static contract: OK")
