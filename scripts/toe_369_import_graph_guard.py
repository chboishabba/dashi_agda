#!/usr/bin/env python3
"""Strict TOE import-graph and ESD read-only regression.

Read-only inspection only. No ESD file is written or renamed.
Requires a local checkout. Does not claim kernel verification.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
AGG = ROOT / "DASHI/EverythingTOESymmetryResolved369.agda"
REQUIRED = (
    "DASHI.Core.SymmetryResolvedFibreExact",
    "DASHI.EverythingSSPRepresentationReductionRound9",
    "DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact",
    "DASHI.Unified.GRQuantumProofTermRegression",
    "DASHI.Governance.FormalisationGovernanceCapstoneExact",
    "DASHI.Core.KernelSemanticClosureBoundaryExact",
    "DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact",
    "DASHI.Mathematics.Topology.AlexanderHornedC3VOAKernelBidiExact",
    "DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact",
    "DASHI.Mathematics.Topology.ExoticHornChronologicalCantorConsumerExact",
    "DASHI.Physics.YangMills.CompactLieInnerC3Exact",
)
FORBIDDEN = ("DASHI.Unifier",)
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z][A-Za-z0-9_.]*)", re.M)
HEAD = re.compile(r"^module\s+([A-Za-z][A-Za-z0-9_.]*)\s+where", re.M)


def audit():
    src = AGG.read_text(encoding="utf-8")
    found = IMPORT.findall(src)
    assert len(found) == len(set(found)), "duplicate TOE imports"
    assert set(REQUIRED) <= set(found), "missing canonical TOE producer"
    assert not set(FORBIDDEN) & set(found), "historical placeholder promoted"
    assert "toeKernelProofDoesNotEstablishSourceSemantics" in src
    assert "toeSelectedVOAActorCannotRecoverSource" in src
    for module in found:
        path = ROOT / (module.replace(".", "/") + ".agda")
        assert path.is_file(), f"unresolved TOE module: {module}"
        source = path.read_text(encoding="utf-8")
        match = HEAD.search(source)
        assert match and match.group(1) == module, f"module/filename mismatch: {module}"
    assert not any("ESD" in name or "digital_esd" in name.lower()
                   for name in found), "unexpected ESD import in focused TOE"
    return {"status": "PASS", "imports": len(found),
            "all_required_source_owners_present": True,
            "historical_unifier_not_imported": True,
            "no_ESD_modules_imported_or_changed": True,
            "kernel_verified": False}


if __name__ == "__main__":
    import json
    print(json.dumps(audit(), indent=2, sort_keys=True))
