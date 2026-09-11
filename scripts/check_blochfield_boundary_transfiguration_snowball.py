from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Culture/BoundaryConservativeTransfigurationBlochfieldExact.agda": [
        "module DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact where",
        "import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution",
        "import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as SnowballOSINT",
        "import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision",
        "import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal",
        "record BoundaryConservativeTransfiguration",
        "socialCountDoesNotCreateAuthority",
        "socialCountDoesNotCreateTruth",
        "laterEvidenceDoesNotSkipUnpaidIdentity",
        '"15K"',
        '"417"',
        '"2K"',
        '"35K"',
    ],
    "DASHI/Culture/Everything.agda": [
        "import DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact",
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
            missing.append(f"{rel}: missing {needle!r}")

if missing:
    raise SystemExit("\n".join(missing))

print("blochfield boundary-transfiguration snowball static check: ok")
