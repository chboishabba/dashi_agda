#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "DASHI/Biology/IBSCausalMaintenanceRegimeExact.agda",
    ROOT / "DASHI/Biology/IBSCausalMaintenanceRegimeRegression.agda",
    ROOT / "DASHI/Biology/IBSResponsePredictorAtlasExact.agda",
    ROOT / "DASHI/Biology/IBSResponsePredictorAtlasRegression.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "canonicalCandidateMaintenanceRegimeAtlas",
    "canonicalRegimeDiscriminationPanel",
    "canonicalCausalMaintenanceParetoFrontier",
    "canonicalMaintenanceCausalEstimandObligation",
    "10.14309/ajg.0000000000003859",
    "10.5056/jnm15067",
    "10.2196/98352",
    "10.1177/17562848261436121",
    "levinthalCitationDoesNotBecomeMichaelLevinCitation",
    "canonicalIBSResponsePredictorAtlas",
    "canonicalIBSResponsePredictionParetoFrontier",
    "10.1016/j.cgh.2026.04.014",
    "10.1186/s40168-021-01188-6",
    "10.1002/ueg2.70204",
    "10.7759/cureus.109142",
    "predictorDoesNotBecomeMediator",
    "internalPredictionDoesNotBecomeClinicalClassifier",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing IBS causal-regime/response surface: " + ", ".join(missing))
forbidden = [
    "symptoms identify the causal regime",
    "predictor proves mediator",
    "AUROC proves clinical utility",
    "David J Levinthal is Michael Levin",
    "one treatment response proves the mechanism",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden IBS promotion surface: " + ", ".join(found))
print("IBS causal-regime/response source surface: OK")
