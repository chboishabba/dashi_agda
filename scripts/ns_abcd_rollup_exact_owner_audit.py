#!/usr/bin/env python3
"""Fail-closed A/B/C/D roll-up audit against source owners, not theorem inference.

Checks which canonical declarations are literal closed/open and distinguishes
source alignment from independently witnessed external proof builds.
No regex over arbitrary comments is used to establish a theorem.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
OWNERS = {
 "A": "DASHI/Physics/Closure/NSClayFacingAPureAnalysisFrontier20261007Exact.agda",
 "B": "DASHI/Physics/Closure/NSClayFacingBPureAnalysisFrontier20261005Exact.agda",
 "ABCD": "DASHI/Physics/Closure/NSABCDMaxCut20261007Exact.agda",
 "CD": "DASHI/Physics/Closure/NSClayFacingCDReleasedAuditFrontier20261007Exact.agda",
 "ProofStatus": "DASHI/Physics/Closure/NSClayFacingABCDProofStatusExact.agda",
}
DECLARED = {
 "A": ["aInternalFrontierClosed","clayPromotion"],
 "B": ["b1PhysicalProducerClosed","b2PhysicalProducerClosed","b3PhysicalProducerClosed","pureAnalysisFrontierClosed","clayPromotion"],
 "ABCD": ["clayPromotion"],
 "CD": ["cDInternalTheoremDiscoveryLane","cDPublicationAuditLane","clayPrizeAdjudicationClaimed"],
}
def audit(root=ROOT):
    result={"schema":"dashi.ns.abcd.rollup.exact_owner_audit.v1","owners":{}}
    for lane,path in OWNERS.items():
        text=(root/path).read_text()
        fields={}
        for symbol in DECLARED.get(lane,[]):
            hits=re.findall(r"(?m)^"+re.escape(symbol)+r"\s*=\s*(true|false)\s*$",text)
            if len(hits)!=1:
                raise ValueError(f"{path}: {symbol} must have exactly one literal Boolean definition")
            fields[symbol]=(hits[0]=="true")
        result["owners"][lane]={"path":path,"literal_flags":fields}
    cd=(root/OWNERS["CD"]).read_text()
    for key in ("independentKernelBuildWitnessedHere","cReleasedDependencyRouteSourceAudited",
                "dReleasedDependencyRouteSourceAudited","releasedNativeProofTermConstructedHere"):
        if not re.search(r"(?m)^"+key+r"\s*:\s*Bool",cd):
            raise ValueError(f"missing CD provenance distinction: {key}")
    if any(result["owners"]["A"]["literal_flags"].values()):
        raise AssertionError("A owner changed: re-audit actual proof terms")
    if any(result["owners"]["B"]["literal_flags"].values()):
        raise AssertionError("B owner changed: re-audit actual proof terms")
    if result["owners"]["ABCD"]["literal_flags"]["clayPromotion"]:
        raise AssertionError("Clay promotion changed without proof audit")
    result["interpretation"]={
        "A_B_all_canonical_physical_leaves_closed":False,
        "C_D_source_alignment_equals_independent_kernel_reproduction":False,
        "scope":"literal owner reconciliation only; imports/aliases require proof-term and kernel audit",
    }
    return result

if __name__=="__main__":
    print(json.dumps(audit(),indent=2,sort_keys=True))
