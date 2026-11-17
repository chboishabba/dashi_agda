#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATHS = [
    ROOT / "DASHI/Unified/FleetFormalGapTOEExact.agda",
    ROOT / "DASHI/Unified/FleetFormalGapTOERegression.agda",
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
]
text = "\n".join(path.read_text(encoding="utf-8") for path in PATHS)

required = [
    "canonicalFleetFormalGapReceipt",
    "canonicalFleetFormalGapMaxCut",
    "namedFormalGapManifestAcquired",
    "584",
    "44",
    "58",
    "74.5526",
    "18.8350",
    "5.5865",
    "itir.pnf.spectral_numeric_abi.v0_2",
    "canonicalPNFSpectralNumericABICoreReceipt",
    "bM2ToR568CompilerClosedIsTrue",
    "canonicalQuantumMereologyBoundary",
    "canonicalGovernedLegalWorkflowTOEInvariantHandoff",
    "toeFleetFormalGapReceipt",
    "unifierFleetFormalGapReceipt",
    "fleetFormalGapTOEReceipt",
]
missing = [name for name in required if name not in text]
if missing:
    raise SystemExit("missing Fleet TOE surface: " + ", ".join(missing))

forbidden = [
    "postulate",
    "allow-unsolved-metas",
    "{-# TERMINATING #-}",
    "{-# NO_POSITIVITY_CHECK #-}",
]
found = [marker for marker in forbidden if marker in text]
if found:
    raise SystemExit("forbidden Fleet TOE trust escape: " + ", ".join(found))

print("Fleet formal-gap TOE source surface: OK")
