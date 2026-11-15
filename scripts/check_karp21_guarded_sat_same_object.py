#!/usr/bin/env python3
"""Fail-closed source dependency regression for guarded Cook--Levin SAT.

Confirms the original SAT/run/cost consumer sites use the SAME guarded
formula and the source-level endcap witness producer is wired. This does
not claim Agda kernel acceptance or prove dependent equalities.
"""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
PREFIX = ROOT / "DASHI/Mathematics/Complexity"
REQUIRED = {
    "ConcreteTapeDecodedTransitionStepExact.agda": [
        "AfterUnique.NoGhostContextBoundaries",
        "interior noGhost",
    ],
    "ConcreteTapeDecodedRunInductionExact.agda": [
        "AfterEndcapsForAllTimes",
        "decodedStepFromEndcaps",
        "AfterUnique.noGhostFromAfterRowEndcaps",
    ],
    "ConcreteTapeDecodedRunLengthExact.agda": [
        "Induction.AfterEndcapsForAllTimes",
        "Induction.decodedStepFromEndcaps",
    ],
    "ConcreteTapeSATToAcceptingRunExact.agda": [
        "Guarded.guardedGlobalCookLevinCNF",
        "Guarded.guardedGlobalCookLevinCNFSound",
        "allEndcaps slot",
        "steps baseBits allEndcaps allSemantic",
    ],
    "ConcreteTapeCookLevinExactBudgetIff.agda": [
        "GuardedCNF.guardedGlobalCookLevinCNF",
        "GuardedCNF.guardedCompletenessFromDecodedEndcaps",
        "EncodedRows.encodedAcceptingAssignmentDecodedEndcaps",
        "Padded.allPaddedRunRowsHavePlainEndcaps",
    ],
    "ConcreteTapeCookLevinCookFormulaExact.agda": [
        "GuardedCNF.guardedGlobalCookLevinCNF",
        "Exact.guardedSATToExactRun",
        "Exact.exactRunToGuardedSAT",
    ],
    "ConcreteTapeCookLevinPrizeFacingExact.agda": [
        "GuardedCNF.guardedGlobalCookLevinCNF",
        "GuardedCount.guardedGlobalClauseBound",
    ],
    "ConcreteTapeCookLevinQuotationGrowthExact.agda": [
        "Guarded.guardedGlobalCookLevinCNF",
        "originalBelowGuarded",
        "Closed.appendLength originalFormula endcapFormula",
    ],
    "ConcreteTapeEncodedPaddedRunDecodeWeldExact.agda": [
        "encodedAcceptanceBaseSameObject",
        "encodedAcceptanceRowSliceSameObject",
        "encodedPaddedRowDecodesSameObject",
        "encodedAcceptingAssignmentDecodedEndcaps",
    ],
}
FORBIDDEN_ORIGINAL = [
    "ConcreteTapeCookLevinCookFormulaExact.agda",
    "ConcreteTapeCookLevinPrizeFacingExact.agda",
]
def main() -> None:
    faults = []
    for name, tokens in REQUIRED.items():
        path = PREFIX / name
        if not path.is_file():
            faults.append(f"{name}: missing source owner")
            continue
        source = path.read_text(encoding="utf8")
        for token in tokens:
            if token not in source:
                faults.append(f"{name}: missing same-object proof/interface {token}")
        if re.search(r"(?m)^\s*postulate\b|\{!|TERMINATING|NON_TERMINATING", source):
            faults.append(f"{name}: admitted proof bypass or hole")
    for name in FORBIDDEN_ORIGINAL:
        source = (PREFIX / name).read_text(encoding="utf8")
        if "GlobalCNF.globalCookLevinCNF" in source:
            faults.append(f"{name}: stale unguarded SAT or cost consumer")
    if faults:
        print("FAIL guarded-SAT source closure:\n" + "\n".join(faults), file=sys.stderr)
        raise SystemExit(1)
    print(f"PASS: {len(REQUIRED)} original guarded SAT/run/cost owners aligned at source level")
    print("NOT AN AGDA KERNEL RECEIPT")

if __name__ == "__main__":
    main()
