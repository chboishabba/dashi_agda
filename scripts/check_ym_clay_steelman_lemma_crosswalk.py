#!/usr/bin/env python3
"""Fail-closed YM continuum steelman / max-cut traceability audit.

Only verifies file identities and matching proof IDs; NEVER upgrades an
Agda, physical, or Clay proof status on the strength of documentation.
"""
from pathlib import Path
import json

IDS=("CLAY4.F1","CLAY4.A1","CLAY4.A2","CLAY4.A3",
     "CLAY4.B1","CLAY4.C1","CLAY4.C2",
     "CLAY4.D1","CLAY4.D2","CLAY4.D3",
     "CLAY4.E1","CLAY4.E2","CLAY4.E3")
DOCS=(
    "Docs/physics/YMClayConstructive4DContinuumSteelman20261106.md",
    "Docs/roadmaps/YMClayExecutionPhasesDeliverablesExactLemmas20261106.md",
    "Docs/roadmaps/YMClayCurrentExactLemmaLedger20261103.md",
    "Docs/roadmaps/ClayYMProofRoadmap.md",
    "Docs/roadmaps/YMClaySteelmanBidirectionalExactRemainingMaxCut20261104.md")
SOURCE="DASHI/Physics/YangMills/YMClayRGLossBudgetToNonGaussianExact.agda"
SCRIPTS=(
  "scripts/check_ym_rg_noncollapse_steelman.py",
  "scripts/check_ym_clay_continuum_bidi_controls.py",
  "scripts/check_ym_marginal_subtracted_uv_tail.py",
)
def audit(root):
    docs={p:(root/p).read_text() for p in DOCS}
    source=(root/SOURCE).read_text()
    for id in IDS:
        for p,s in docs.items():
            assert id in s, (p, id, "missing exact proof leaf")
    for name in ("referenceRGUniformNoncollapse",
        "asOriginalT5Nontriviality","continuumRGChargeIsNonzero",
        "finiteRGLoss", "embedPreservesOrder"):
        assert name in source, ("new golden helper missing",name)
    regression=(root/"DASHI/Unified/BalabanRGTOERegression.agda").read_text()
    assert SOURCE.rsplit("/",1)[-1][:-5] in regression
    workflow=(root/".github/workflows/ym-native-maxcut-exact-agda.yml").read_text()
    assert SOURCE in workflow
    for script in SCRIPTS:
        assert (root/script).is_file()
        assert script in workflow, ("not CI-integrated",script)
    assert "independently owned" not in source
    return {"result":"PASS_DOCUMENT_AND_SOURCE_TRACEABILITY",
            "exact_lemma_ids":len(IDS),"crosswalk_documents":len(DOCS),
            "new_source":SOURCE,
            "Agda_kernel_receipt":"NOT_INFERRED",
            "physical_YM_or_Clay_proof":"NOT_INFERRED"}

if __name__=="__main__":
    print(json.dumps(audit(Path(__file__).resolve().parents[1]),indent=2))
