from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact.agda": [
        "module DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact where",
        "localRegionalCumulativeAnalysisRequired",
        "surroundingProjectMapDoesNotPayCumulativeAnalysis",
        "pastFragmentationDoesNotLowerMarginalValueByDefinition",
        "mappedCorridorScoreDoesNotPayFunctionalConnectivity",
        "retentionDoesNotEqualAdditionalGain",
        "secondarySourceDoesNotPayPrimaryFact",
        "apparentGapDoesNotEqualLegalInvalidity",
        "finalPDMayStillPayResidual",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogarooEPBC8575CumulativeImpactSufficiencyExact"
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

print("Woogaroo cumulative-impact sufficiency static contract: OK")
