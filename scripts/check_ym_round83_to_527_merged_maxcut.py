#!/usr/bin/env python3
"""Fail-closed 43-leaf YM source/max-cut ledger against original Agda owners.

Verifies the exact R515/R518 source leaves, no lost/duplicated obligations,
the four/six/seven/five counts, and explicit non-43 mathematical gates.
This is a SOURCE LEDGER checker, NOT an Agda kernel or Clay theorem check.
"""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path

MANIFEST = Path("Docs/roadmaps/YMClayRound83Round84Round87Round518Round527MergedMaxCut20261114.json")
BASE = Path("DASHI/Physics/YangMills")

def block(source: str, field: str) -> list[str]:
    match = re.search(r"(?m)^" + re.escape(field) +
        r"\s*=\s*([\s\S]*?)\s*∷\s*\[\]", source)
    if match is None:
        raise ValueError(f"missing explicit source list: {field}")
    return re.findall(r"(?:R496\.)?([a-zA-Z][a-zA-Z0-9_]*)\s*∷", match.group(1) + " ∷ []")

def checked_count(source: str, name: str, expected: int) -> None:
    regex = r"(?m)^" + re.escape(name) + r"\s*=\s*" + str(expected) + r"\s*$"
    if not re.search(regex, source):
        raise ValueError(f"count owner drift: {name} != {expected}")

def inspect(repo: Path) -> dict:
    ledger = json.loads((repo / MANIFEST).read_text(encoding="utf-8"))
    def src(file: str) -> str:
        return (repo / BASE / file).read_text(encoding="utf-8")

    r515 = src("YangMillsClayPostQuantitativeResidualRound515Exact.agda")
    r518 = src("YangMillsClayPostStructuralT1ResidualRound518Exact.agda")
    expected = {
        "source_analysis": block(r515, "sourceAnalysisLeaves"),
        "source_attachment": block(r515, "sourceLiteralAttachmentLeaves"),
        "endpoint_semantic": block(r518, "remainingEndpointSemanticLeaves"),
        "source_bundle": block(r518, "addedSourceLeaves"),
    }
    for layer, count in [("source_analysis",15),("source_attachment",18),
                          ("endpoint_semantic",8),("source_bundle",2)]:
        if len(expected[layer]) != count:
            raise ValueError(f"source length drift: {layer}, {len(expected[layer])}")
    if ledger["round518_reconciliation"] != {
        "source_analysis":15,"source_attachment":18,"endpoint_semantic":8,
        "source_bundle":2,"total":43,
    }:
        raise ValueError("ledger source-count metadata drift")

    actual: dict[str,list[str]] = {name:[] for name in expected}
    for row in ledger["entries"]:
        if row["layer"] not in actual:
            raise ValueError("unknown ledger layer " + row["layer"])
        if row["status"] != "open_source_instantiation":
            raise ValueError("unverified physical gate promoted: " + row["id"])
        if row["controlling_cut"] == "unmapped":
            raise ValueError("lost source owner for " + row["id"])
        actual[row["layer"]].append(row["id"])
    if actual != expected or sum(map(len,actual.values())) != 43:
        raise ValueError("43 original source leaves lost, duplicated, or reordered")

    counts = ledger["research_counts"]
    if counts != {
        "round83_seven_named_physical_roles":7,
        "round84_independent_analytic_families":6,
        "round87_frozen_clay_research_rows":4,
        "round527_C_source_packages":5,
    }:
        raise ValueError("research-level count mismatch")
    for file, n, count in [
        ("BalabanClayHighestAlphaRound83SevenAnalyticLemmaExact.agda",
         "round83HardAnalyticLemmaUpperCount",7),
        ("BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda",
         "round84HardAnalyticLemmaUpperCount",6),
        ("BalabanClayHighestAlphaRound87FourAnalyticLemmaExact.agda",
         "round87ShortestClayAnalyticCount",4),
        ("YangMillsClayCPhysicalPackageMaxCutRound527Exact.agda",
         "cPhysicalPackageCount",5),
    ]:
        checked_count(src(file), n, count)
    required_non43 = {"E1","D2","N1","G1","L1.literal_P0","L3.heat",
                      "L7.same_OS_charge","legacy_real_trust","G2_source_witness"}
    found = {row["gate"] for row in ledger["outside_43_mandatory"]}
    if required_non43 != found:
        raise ValueError("outside-43 physical/trust gates not preserved")
    if not ledger["promotion"] == {
        "round518_43_open":True, "round84_6_closed":False,
        "round87_4_closed":False,"agda_kernel_accepted":False,
    }:
        raise ValueError("unverified theorem promotion")
    return {"status":"PASS_SOURCE_LEDGER_ONLY",
            "source_analysis":15,"source_attachment":18,
            "endpoint_semantics":8,"source_bundles":2,"mapped":43,
            "supplementary_gates":len(found),"kernel_accepted":False}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo",type=Path,default=Path.cwd())
    parser.add_argument("--json",action="store_true")
    args=parser.parse_args()
    try:
        result=inspect(args.repo)
    except (OSError,ValueError,KeyError,TypeError,json.JSONDecodeError) as e:
        parser.exit(2, "BLOCKED: " + str(e) + "\n")
    if args.json:
        print(json.dumps(result,indent=2))
    else:
        print("PASS: 43/43 original YM R518 residuals mapped; "
              "7/6/4/5 scoreboards reconciled; NO KERNEL RECEIPT")

if __name__ == "__main__":
    main()
