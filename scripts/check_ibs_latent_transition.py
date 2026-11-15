#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "DASHI/Biology/IBSLatentStateTransitionExact.agda",
    ROOT / "DASHI/Biology/IBSLatentStateTransitionRegression.agda",
    ROOT / "DASHI/Biology/IBSTransitionTriggerAtlasExact.agda",
    ROOT / "DASHI/Biology/IBSTransitionTriggerAtlasRegression.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.1016/j.cell.2020.08.007",
    "10.1111/nmo.13514",
    "10.1016/j.cgh.2026.05.008",
    "10.3389/frmbi.2026.1884540",
    "10.3748/wjg.v29.i21.3241",
    "10.1111/nmo.70133",
    "10.1111/nmo.70232",
    "canonicalTemporalStateEvidenceAtlas",
    "canonicalIBSTransitionParetoFrontier",
    "canonicalIBSTemporalPathBoundary",
    "canonicalIBSTransitionTriggerAtlas",
    "canonicalTransitionTriggerParetoFrontier",
    "trajectoryClusterDoesNotValidateAttractor",
    "flareRemissionDifferenceDoesNotProveHysteresis",
    "postInfectiousPersistenceDoesNotValidateAttractor",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS latent-transition surface: " + ", ".join(missing))
forbidden = [
    "IBS is an attractor",
    "flare proves hysteresis",
    "stress causes IBS by definition",
    "wearable HRV identifies IBS state",
    "post-infectious IBS proves a unique mechanism",
    "trajectory cluster is a validated attractor",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden promotion surface found: " + ", ".join(found))
print("IBS latent-transition source surface: OK")
