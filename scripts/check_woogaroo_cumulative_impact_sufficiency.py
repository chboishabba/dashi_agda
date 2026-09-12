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
        "EPBC 2020/8651",
        "EPBC 2020/8629",
        "EPBC 2018/8350",
        "EPBC 2017/7875",
        "EPBC 2016/7676",
        "EPBC 2014/7306",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationSourceAtlasExact.agda": [
        "springfield8575January2026PreliminaryDocumentation",
        "9612 Springfield Preliminary Documentation v5 — EPBC 2019/8575",
        "source identity is kept distinct",
    ],
    "DASHI/Law/SensibLawWoogarooLegalPriorityRoadmapExact.agda": [
        "cumulativeImpactSufficiency",
        "Item 4.6(c)",
        "Final PD",
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
