from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogarooPreservationRoadmapExact.agda": [
        "local9281ExecutionGateLane",
        "condition6aExecutionGate",
        "condition6aBeforeEmergencyCourtTheory",
        "currentHighestAlphaPath",
    ],
    "DASHI/Law/SensibLawWoogarooCounselHandoffExact.agda": [
        "condition6aExecutionCounselIssue",
        "condition6aRecordBeforeContraventionOpinion",
    ],
    "Docs/SaveWoogarooForestLegalTeamBrief.md": [
        "9281/2024/OW execution gate",
        "Condition 6(a)",
        "signed same-clearing-phase Environmental Pre-Clearance Package",
        "public non-location is not proof of non-submission",
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

print("Woogaroo handoff reconciliation static contract: OK")
