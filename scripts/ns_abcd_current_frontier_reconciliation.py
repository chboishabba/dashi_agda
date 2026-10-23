#!/usr/bin/env python3
"""Current NS A/B/C/D proof-frontier reconciliation, strict about false leaves.

Reads literal declarations in existing Agda owners. Does not infer a mathematical
proof from a Boolean status declaration or imported source-alignment statement.
"""
from pathlib import Path
import hashlib, json, re

ROOT=Path(__file__).resolve().parents[1]
FILES={
 "A_same_object":"DASHI/Physics/Closure/NSClayFacingAPhysicalSameObjectCutExact.agda",
 "B_preferred_R832":"DASHI/Physics/Closure/NSTriadKNR650Rational345DecisionMaxCutRound832Exact.agda",
 "B_legacy":"DASHI/Physics/Closure/NSClayFacingBPureAnalysisFrontier20261005Exact.agda",
 "C_D_source":"DASHI/Physics/Closure/NSClayFacingCDReleasedAuditFrontier20261007Exact.agda",
 "ABCD_rollup":"DASHI/Physics/Closure/NSABCDMaxCut20261007Exact.agda",
 "Clay_propositions":"DASHI/Physics/Closure/NSConcreteLiteralClayABCDRunTargetExact.agda",
 "R851_zero_mode":"DASHI/Physics/Closure/NSTriadKNR650Rational345FullForcingSupportRound851Exact.agda",
 "R852_vector":"DASHI/Physics/Closure/NSTriadKNR650Rational345FullVectorEvaluationRound852Exact.agda",
}
EXPECTED_FALSE={
 "A_same_object": ["aActualKernelSameObjectInstantiationClosedHere",
                   "aFiniteEnergyMajorantIdentificationClosedHere"],
 "B_legacy":["b1PhysicalProducerClosed","b2PhysicalProducerClosed",
             "b3PhysicalProducerClosed","pureAnalysisFrontierClosed"],
 "B_preferred_R832":[],
 "ABCD_rollup":["clayPromotion"],
}
LEAVES=["concreteRepositoryVectorEvaluation","concreteRealFiniteODETransport"]

def reconcile(root=ROOT):
    report={"schema":"dashi.ns.abcd.current_frontier_reconciliation.v1","sources":{}}
    for name,relative in FILES.items():
        content=(root/relative).read_text(encoding="utf-8")
        reported={}
        for var in EXPECTED_FALSE.get(name,()):
            match=re.findall(r"(?m)^"+re.escape(var)+r"\s*=\s*(true|false)\s*$",content)
            if match!=["false"]:
                raise ValueError(f"{name}: changed or missing {var}; review proof dependencies")
            reported[var]=False
        if name=="B_preferred_R832":
            closed = re.findall(
                r"(?m)^decisionLeafClosed\\s+concreteRepositoryVectorEvaluation\\s*=\\s*\\n\\s*(R852\\.[A-Za-z0-9_]+)\\s*$",
                content,
            )
            if closed != ["R852.round852FullR829DRepositoryVectorRecordInhabited"]:
                raise ValueError("R832 R829D proof owner changed: inspect proof terms")
            remaining = re.findall(
                r"(?m)^decisionLeafClosed\\s+concreteRealFiniteODETransport\\s*=\\s*(true|false)\\s*$",
                content,
            )
            if remaining != ["false"]:
                raise ValueError("R832 real ODE transport status changed")
            reported["concreteRepositoryVectorEvaluation_source_written"] = True
            reported["concreteRealFiniteODETransport"] = False
        if name=="R851_zero_mode":
            if "R436.projectedNonlinearityAtZeroIsZero" not in content or "R848.mixedFilterEmptyAtInactiveNonzero" not in content:
                raise ValueError("R851 lost the disjoint zero/nonzero mode proof")
        if name=="R852_vector":
            if "physicalR829D = R.activeEvaluationBuildsR829D activeVectors" not in content:
                raise ValueError("R852 physical R829D construction missing")
        report["sources"][name]={
            "path":relative,
            "sha256":hashlib.sha256(content.encode()).hexdigest(),
            "explicit_open":reported,
        }
    report["reconciliation"]={
        "preferred_periodic_B":"R823-R832 signed reserve, not old B4-only path",
        "R832_concrete_vector_evaluation_source_written":True,
        "R832_concrete_vector_evaluation_kernel_checked_here":False,
        "R832_real_ODE_transport_closed":False,
        "A_physical_same_object_closed":False,
        "legacy_B_analytic_frontier_closed":False,
        "C_D_claim":"repository asserts external released proof/source correspondence; no independent kernel validation supplied by this audit",
        "Clay_proof_verified_by_this_audit":False,
    }
    return report

if __name__=="__main__":
    print(json.dumps(reconcile(),sort_keys=True,indent=2))
