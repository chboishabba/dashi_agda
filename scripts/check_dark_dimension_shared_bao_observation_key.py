from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionSharedBAOObservationKeyExact.agda": [
        "module DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact where",
        "DESIDR2TracerBin",
        "lrg1", "lrg2", "lrg3Elg1", "elg2", "qso", "lya",
        "SharedBAOObservationKey",
        "lrg1TransverseKey", "lrg1RadialKey",
        "lrg2TransverseKey", "lrg2RadialKey",
        "lrg3Elg1TransverseKey", "lrg3Elg1RadialKey",
        "elg2TransverseKey", "elg2RadialKey",
        "qsoTransverseKey", "qsoRadialKey",
        "lyaTransverseKey", "lyaRadialKey",
        "sameObservationKeyRequirement",
        "sameObservableDifferentKeyIsNotSameObservation",
        "sharedObservationKeyIdentityPaid",
        "sameKeyNumericalModelPredictionsStillOpen",
        "10.1103/tr6y-kpc6",
    ],
    "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda": [
        "import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey",
        "sameObservationKeyStillRequiredForProspectiveSeparation",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_shared_bao_observation_key.py",
        "DASHI/Empirical/DarkDimensionSharedBAOObservationKeyExact.agda",
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

print("Dark-dimension shared BAO observation-key static contract: OK")
