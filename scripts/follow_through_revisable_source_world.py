#!/usr/bin/env python3
"""Claim-relative, revisable evidence world for historical Follow Through."""
import json
import sys
from pathlib import Path

STATES = {"present", "notLocated", "knownAbsent"}
LEVELS = {"sourceReported", "independentlyReproduced", "conditional", "unresolved"}
def validate(world):
    roots = {s["id"]: s for s in world["sources"]}
    if len(roots) != len(world["sources"]): raise ValueError("duplicate roots")
    evidence = {e["id"]: e for e in world["evidence"]}
    if len(evidence) != len(world["evidence"]): raise ValueError("duplicate evidence")
    claims = {c["id"]: c for c in world["claims"]}
    if len(claims) != len(world["claims"]): raise ValueError("duplicate claims")
    for e in world["evidence"]:
        if e["status"] not in STATES: raise ValueError("invalid status")
        if e["root"] not in roots: raise ValueError("unknown source root")
        if e["status"] == "present" and not e.get("locator"): raise ValueError("present needs locator")
        if e["status"] == "knownAbsent" and not e.get("absence_scope"): raise ValueError("known absent needs scope")
    for c in world["claims"]:
        if c["level"] not in LEVELS: raise ValueError("invalid claim level")
        if not c.get("statement") or not c.get("scope"): raise ValueError("unscoped claim")
        for k in c["requires"]:
            if k not in evidence: raise ValueError("unknown prerequisite")
        for k in c.get("supports", []):
            if k not in evidence: raise ValueError("unknown support")
        severe=c.get("severe_test")
        if severe is None or not all(severe.get(k) for k in ("would_narrow","would_strengthen","test_status")):
            raise ValueError("claim lacks bidirectional severe test")
        if severe["test_status"] not in {"notRun","sourceChecked","executed"}:
            raise ValueError("invalid severe test status")
        if c["level"] == "independentlyReproduced":
            if not c.get("reproduction_receipt"): raise ValueError("unsupported reproduction promotion")
    actions = {a["id"]: a for a in world["actions"]}
    if len(actions) != len(world["actions"]): raise ValueError("duplicate action")
    for a in world["actions"]:
        if not a["targets"] or not set(a["targets"]) <= evidence.keys(): raise ValueError("bad target")
        if len(a["cost"]) != 3 or any(not isinstance(x, int) or x < 0 for x in a["cost"]): raise ValueError("bad cost")
    return evidence

def report(world):
    e = validate(world)
    claims = {}
    root_by_evidence = {item["id"]: item["root"] for item in world["evidence"]}
    for c in world["claims"]:
        missing = sorted(k for k in c["requires"] if e[k]["status"] != "present")
        supports = c.get("supports", [])
        roots = sorted({root_by_evidence[k] for k in supports})
        claims[c["id"]] = {"level":c["level"],"supported_by":supports,
                           "source_roots":roots, "independent_root_count":len(roots),
                           "unpaid":missing, "prerequisites_located":not missing,
                           "severe_test":c["severe_test"],
                           "note":"Located prerequisites do not establish causal identification, source authenticity, or reproduced evidence"}
    candidates = []
    for a in world["actions"]:
        live = sorted(k for k in a["targets"] if e[k]["status"] == "notLocated")
        consumers = sorted(c["id"] for c in world["claims"] if set(live)&set(c["requires"]))
        if live and consumers:
            candidates.append({"action":a["id"],"reopens":consumers,
                               "evidence_targets":live,"cost":a["cost"]})
    def dominates(a,b):
        return set(a["reopens"])>=set(b["reopens"]) and set(a["evidence_targets"])>=set(b["evidence_targets"]) and all(x<=y for x,y in zip(a["cost"],b["cost"])) and (set(a["reopens"])!=set(b["reopens"]) or set(a["evidence_targets"])!=set(b["evidence_targets"]) or a["cost"]!=b["cost"])
    frontier = [a for a in candidates if not any(dominates(b,a) for b in candidates if b is not a)]
    # Hypothetical effect only: no mutation of statuses, no claims upgraded.
    return {"claims":claims,"pareto_frontier":sorted(frontier,key=lambda x:x["action"]),
            "candidate_actions":sorted(candidates,key=lambda x:x["action"])}

if __name__ == "__main__":
    print(json.dumps(report(json.loads(Path(sys.argv[1]).read_text())),indent=2,sort_keys=True))
