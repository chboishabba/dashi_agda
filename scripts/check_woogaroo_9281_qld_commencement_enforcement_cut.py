from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Law/SensibLawWoogaroo9281QueenslandCommencementEnforcementCutExact.agda": [
        "module DASHI.Law.SensibLawWoogaroo9281QueenslandCommencementEnforcementCutExact where",
        "planningAct2016CurrentSource",
        "section72CommencementGate",
        "section164ApprovalComplianceOffence",
        "section180AnyPersonEnforcementRoute",
        "section180FutureOffenceInterimRoute",
        "condition6aFeedsSection72Gate",
        "condition6aUnsatisfiedDoesNotByItselfProveDevelopmentOffence",
        "publicRegisterSilenceDoesNotPaySection72NonCompliance",
        "qldCutDoesNotReplaceFederalCut",
        "canonicalQueenslandPreservationCut",
    ],
    "DASHI/Law/SensibLawWoogarooPreservationEverything.agda": [
        "import DASHI.Law.SensibLawWoogaroo9281QueenslandCommencementEnforcementCutExact"
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

print("Woogaroo 9281 Queensland commencement/enforcement cut static contract: OK")
