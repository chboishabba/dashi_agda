from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDAOSameKeyReconstructionRunExact.agda": [
        "module DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact where",
        "DAOSameKeyReconstructionRunStatus",
        "upstreamRevisionPinned",
        "paperTableReconstructionSelected",
        "allSixDESIKeysRequested",
        "executionReceiptPresent",
        "numericalVectorPresent",
        "reconstructionRunStillOpen",
        "originalPaperManifestNotClaimed",
        "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9",
        "0.510",
        "0.706",
        "0.934",
        "1.321",
        "1.484",
        "2.330",
    ],
    "scripts/run_dark_dimension_dao_same_key_reconstruction.py": [
        "from classy import Class",
        "from reconstruct_dark_dimension_dao_paper_table_manifest import build_manifest",
        "DRMD_CLASS_REVISION = \"aa2b61a0f1cf246672cdbd4634a4797d4cc654f9\"",
        '"lrg1": 0.510',
        '"lrg2": 0.706',
        '"lrg3_elg1": 0.934',
        '"elg2": 1.321',
        '"qso": 1.484',
        '"lya": 2.330',
        "cosmo.angular_distance(z)",
        "cosmo.Hubble(z)",
        "cosmo.rs_drag",
        '"manifest_kind": "paper-table-reconstruction"',
        '"original_paper_manifest_claimed": False',
        '"DM_over_rd"',
        '"DH_over_rd"',
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "dao-reconstruction-runtime:",
        "NEDE-Cosmo/DRMD-CLASS.git@aa2b61a0f1cf246672cdbd4634a4797d4cc654f9",
        "python scripts/run_dark_dimension_dao_same_key_reconstruction.py",
        "dao-same-key-reconstruction.json",
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

print("Dark-dimension DAO same-key reconstruction runner static contract: OK")
