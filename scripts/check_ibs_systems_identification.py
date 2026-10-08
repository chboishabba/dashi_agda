#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "DASHI/Biology/IBSGutBrainImmuneSystemsHyperfabricExact.agda",
    ROOT / "DASHI/Biology/IBSSystemsIdentificationParetoExact.agda",
    ROOT / "DASHI/Biology/IBSSystemsIdentificationParetoRegression.agda",
    ROOT / "DASHI/Biology/IBSMechanismProbePerturbationAtlasExact.agda",
    ROOT / "DASHI/Biology/IBSMechanismProbePerturbationRegression.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.1186/s40168-022-01450-5",
    "10.1007/s11894-026-01053-2",
    "10.3389/fnins.2026.1832540",
    "10.1016/j.ejim.2024.07.008",
    "10.1016/j.cgh.2026.04.014",
    "10.1053/j.gastro.2024.02.008",
    "10.1016/j.cgh.2020.02.021",
    "10.1111/apt.12319",
    "canonicalIBSMeasurementAtlas",
    "canonicalMinimumDiscriminatingPanel",
    "canonicalIBSSystemsParetoFrontier",
    "canonicalIBSMechanismProbeAtlas",
    "canonicalIBSProbeParetoFrontier",
    "singleMarkerDoesNotIdentifyWholeSystemState",
    "crossSectionDoesNotIdentifyFeedbackDirection",
    "responseDoesNotIdentifyUniqueMechanism",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS systems-identification surface: " + ", ".join(missing))
forbidden = [
    "one biomarker identifies IBS mechanism",
    "IBS-D is bile acid diarrhoea",
    "same symptom response means same mechanism",
    "target engagement proves whole system closure",
    "cross sectional omics proves feedback direction",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden IBS systems promotion surface found: " + ", ".join(found))
print("IBS systems-identification source surface: OK")
