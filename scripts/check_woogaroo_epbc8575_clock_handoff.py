from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogarooCounselHandoffExact.agda": [
        "federalClockManifestationCounselIssue",
        "portalStatusBeforeLegalStateFirewall",
        "ministerReceiptDateBeforeClockReconstruction",
    ],
    "DASHI/Law/SensibLawWoogarooLegalPriorityRoadmapExact.agda": [
        "condition6aPriority",
        "federalClockReceipt",
        "ministerReceiptResidual",
        "localExecutionGateFirst",
        "federalDecisionParallelSecond",
    ],
    "Docs/SaveWoogarooForestLegalTeamBrief.md": [
        "Portal status and s 95B / s 130 clock correction",
        "publication is not the statutory clock trigger by itself",
        "more than 850",
        "exact official submission total remains open",
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    p = ROOT / rel
    if not p.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = p.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Woogaroo EPBC 8575 clock handoff static contract: OK")
