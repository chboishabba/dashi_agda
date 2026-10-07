#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [
    ROOT / "DASHI/Biology/QuailEggHistamineGutSnowballExact.agda",
    ROOT / "DASHI/Biology/QuailEggHistamineGutSnowballRegression.agda",
    ROOT / "DASHI/Biology/QuailEggHistamineGutParetoSnowballExact.agda",
    ROOT / "DASHI/Biology/QuailEggHumanOralTransferExact.agda",
    ROOT / "DASHI/Biology/QuailEggHumanOralTransferRegression.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in paths)
required = [
    "10.29219/fnr.v62.1084",
    "10.1016/j.fshw.2022.09.028",
    "10.1126/scitranslmed.abj1895",
    "10.1053/j.gastro.2015.12.034",
    "10.3390/nu13041262",
    "10.3389/fmicb.2020.01130",
    "10.1002/fsn3.147",
    "10.1017/S0022215122001219",
    "canonicalGutHistamineCompartmentWeld",
    "canonicalQuailEggIBSExperimentRequirement",
    "canonicalGutAcquisitionFrontier",
    "canonicalQuailHumanOralTransferBoundary",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing quail/histamine snowball surface: " + ", ".join(missing))
forbidden = [
    "quail egg cures IBS",
    "serum DAO equals gut DAO",
    "recombinant ovomucoid equals whole quail egg",
    "fermented fish pH proves gut pH",
    "rhinitis trial proves IBS efficacy",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden promotion surface found: " + ", ".join(found))
print("quail/histamine gut snowball source surface: OK")
