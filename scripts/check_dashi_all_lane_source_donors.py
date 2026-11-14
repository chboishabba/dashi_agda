#!/usr/bin/env python3
"""Fail-closed, multi-lane, exact-head source donor/consumer ledger validator.

This validates ownership, dependency-status consistency and optional exact
git-object presence. It is NOT Agda/Lean typechecking, a mathematical proof,
an authoritative proof world, or a claim of Clay progress.

Run on #1499 checkout:
  python3 scripts/check_dashi_all_lane_source_donors.py
  python3 scripts/check_dashi_all_lane_source_donors.py --verify-local-objects

The second command requires all exact donor commits in the local Git object
database, obtainable through user-controlled pinned fetch/worktrees; it never
performs network access, runs a checker, or alters repository history.
"""
from __future__ import annotations
import argparse
import json
import re
import subprocess
from pathlib import Path
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "Docs/roadmaps/DASHIAllLaneSourceDonorMaxCut20261113.json"
LANES = {"BISHOP", "KARP21", "BSD", "NS", "RH", "HODGE", "WORLD", "YM", "VOA", "BIOLOGY", "CYBERSYN"}
TYPES = {"new_mathematics", "analytic_source", "arithmetic_source",
         "formalization", "formal_weld", "source_weld", "integration"}
ALLOWED_REPOS = {"chboishabba/dashi_agda", "chboishabba/dashi_lean4"}
SHA40 = re.compile(r"[0-9a-f]{40}\Z")
ID = re.compile(r"[A-Z][A-Z0-9-]+\Z")
SINGLE_SOURCE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")

class SourceAuditError(RuntimeError):
    pass

def _safe_path(path: str) -> bool:
    return (type(path) is str and path and path[0] != "/"
            and "\\" not in path and ".." not in path.split("/")
            and (path.endswith(".agda") or path.endswith(".lean")
                 or path.endswith(".py")))

def verify(document: dict, *, verify_local_objects: bool = False, root: Path = ROOT):
    assert document["claim_no_clay_problem_solved"] is True
    assert document["no_kernel_acceptances_obtained"] is True
    assert document["source_terminal_gates_closed_here"] == 0
    heads = document["heads"]
    assert len(heads) >= 20
    head_index = {}
    for head in heads:
        assert head["repository"] in ALLOWED_REPOS
        assert type(head["pr"]) is int and head["pr"] > 0
        assert SHA40.fullmatch(head["sha"])
        assert type(head["branch"]) is str and head["branch"]
        key = (head["repository"], head["pr"])
        assert key not in head_index, "duplicate PR head"
        head_index[key] = head
    rows = document["bridges"]
    ids = [x["id"] for x in rows]
    assert len(ids) >= 19 and len(ids) == len(set(ids))
    assert all(ID.fullmatch(i) for i in ids)
    assert {r["lane"] for r in rows} == LANES
    assert sum(r["lane"] == "BISHOP" for r in rows) >= 3
    assert sum(r["lane"] == "KARP21" for r in rows) >= 3
    assert sum(r["lane"] == "BSD" for r in rows) >= 3
    classified = Counter()
    for row in rows:
        assert row["classification"] in TYPES
        assert row["cross_branch_state"] and row["missing"]
        assert row["consumer"] and row["paid"]
        assert row["kernel_accepted_in_this_reconciliation"] is False
        assert row["terminal_gate_closed"] is False
        assert row["source_weld_promotion"] is False
        donors = row["donors"]
        assert donors and len(donors) <= 6
        for donor in donors:
            key = next(((h["repository"], h["pr"]) for h in heads
                        if h["pr"] == donor["pr"]), None)
            assert key in head_index, f"unowned donor {donor}"
            assert _safe_path(donor["path"]), donor["path"]
            assert donor["github_exact_head_source_readback"] is True
            assert donor["github_exact_head_decl_seen"] is True
            assert donor["github_head_sha_observed"] == head_index[key]["sha"]
            assert type(donor["declaration"]) is str and donor["declaration"]
            if "exact path to confirm" in donor["declaration"].lower():
                raise SourceAuditError("unresolved provisional donor")
            if verify_local_objects:
                head = head_index[key]
                obj = f'{head["sha"]}:{donor["path"]}'
                got = subprocess.run(["git", "-C", str(root), "show", obj],
                                     capture_output=True, text=True, check=False)
                if got.returncode:
                    raise SourceAuditError(f"missing exact head blob {obj}")
                symbol = donor["declaration"]
                # Some rows explicitly name a conceptual proof owner instead
                # of an exact declaration. Require an actual code token only
                # when it is a single syntactic identifier.
                if SINGLE_SOURCE.fullmatch(symbol) and not re.search(
                        rf"(?<![\w']){re.escape(symbol)}(?![\w'])", got.stdout):
                    raise SourceAuditError(f"missing donor term: {obj}::{symbol}")
        classified[row["lane"]] += 1
    counts = document["source_readback_counts"]
    assert counts["donor_files"] == sum(len(r["donors"]) for r in rows)
    assert counts["identifier_seen"] == counts["donor_files"]
    assert counts["unverified_terms"] == 0
    assert counts["agda_lean_kernel_receipts"] == 0
    lookup = {r["id"]: r for r in rows}
    assert lookup["BISHOP-ETA-EXP"]["cross_branch_state"] == "source_dependencies_co_located_on_pr1478_kernel_unverified"
    assert lookup["BISHOP-ETA-EXP"]["kernel_accepted_in_this_reconciliation"] is False
    assert lookup["BISHOP-ETA-EXP"]["source_weld_promotion"] is False
    assert lookup["BISHOP-ETA-TAIL"]["cross_branch_state"] == "source_dependencies_co_located_on_pr1478_kernel_unverified"
    assert "log(2n)" in lookup["BISHOP-ETA-EXP"]["missing"]
    assert "dyadic" in lookup["BISHOP-ETA-EXP"]["missing"]
    assert "uniform" in lookup["BISHOP-ETA-TAIL"]["missing"].lower()
    # Original Bishop eta source is now co-located, and its dyadic scaling
    # has a concrete TWO-LEAF proof reduction. Requiring these exact status
    # flags prevents source-written implications becoming analytic results.
    p2 = lookup["BISHOP-ETA-EXP"]["p2_dyadic_source_reduction"]
    assert p2["pr"] == 1478
    assert p2["pinned_pr_sha"] == head_index[
        ("chboishabba/dashi_agda", 1478)]["sha"]
    assert p2["owner"] == (
        "DASHI/Analysis/BishopOriginalEtaDyadicSourceLawReductionExact.agda")
    assert _safe_path(p2["owner"]) and p2["source_readback"] is True
    assert p2["source_written"] is True
    assert set(p2["declarations"]) == {
        "originalDyadicNegativeSLogIsSum",
        "originalEtaDyadicScaleFromLogAndExp",
        "originalRound11EtaZetaFiniteFromTwoLaws",
    }
    for flag in ("agda29_kernel_accepted",
                 "original_log_dyadic_law_inhabited",
                 "original_native_complex_exp_add_inhabited",
                 "unconditional_original_dyadic_proved",
                 "compact_uniform_eta_convergence_proved",
                 "terminal_gate_closed"):
        assert p2[flag] is False, ("unauthorized eta proof promotion", flag)
    if verify_local_objects:
        ref = p2["pinned_pr_sha"] + ":" + p2["owner"]
        got = subprocess.run(
            ["git", "-C", str(root), "show", ref],
            capture_output=True, text=True, check=False)
        if got.returncode:
            raise SourceAuditError("missing eta dyadic source " + ref)
        for name in p2["declarations"]:
            if not re.search(rf"(?<![\\w']){re.escape(name)}(?![\\w'])",
                             got.stdout):
                raise SourceAuditError("missing eta source theorem " + name)
    assert lookup["BISHOP-ETA-TAIL"]["terminal_gate_closed"] is False
    # Original source P1.L is credited without converting the still
    # uninhabited R4 square-root calculus into a theorem.
    p1l = lookup["BISHOP-KOENIGS-LOG"]["p1l_original_source"]
    assert p1l["pr"] == 1478
    assert p1l["pinned_pr_sha"] == head_index[
        ("chboishabba/dashi_agda", 1478)]["sha"]
    assert p1l["true_displacement_constant"] == "8/27"
    assert p1l["source_readback"] is True
    assert p1l["uses_existing_uninhabited_root_calculus"] is True
    assert p1l["kernel_elaborated"] is False
    assert p1l["unconditional_semantic_proof"] is False
    assert p1l["terminal_gate_closed"] is False
    for owner, decl in (
        ("finite_to_limit_owner", "finite_to_limit_declaration"),
        ("selected_numeric_owner", "selected_numeric_declaration"),
    ):
        assert _safe_path(p1l[owner])
        assert SINGLE_SOURCE.fullmatch(p1l[decl])
        if verify_local_objects:
            obj = p1l["pinned_pr_sha"] + ":" + p1l[owner]
            got = subprocess.run(["git", "-C", str(root), "show", obj],
                                 capture_output=True, text=True, check=False)
            if got.returncode or not re.search(
                    rf"(?<![\w']){re.escape(p1l[decl])}(?![\w'])",
                    got.stdout):
                raise SourceAuditError("missing original Bishop P1.L source " + obj)
    assert lookup["WORLD-1495-1484"]["cross_branch_state"] == "divergent_stack_unjoined"
    assert lookup["NS-R850-R830"]["terminal_gate_closed"] is False
    assert lookup["KARP-G3"]["terminal_gate_closed"] is False
    assert lookup["BSD-K1-K3"]["terminal_gate_closed"] is False
    assert lookup["BIOLOGY-BH4-PNP"]["cross_branch_state"] == "not_present_together"
    assert lookup["VOA-Y443-FLM"]["terminal_gate_closed"] is False
    assert lookup["CYBERSYN-WORLD"]["terminal_gate_closed"] is False
    return {"heads": len(heads), "bridges": len(rows),
            "donors": sum(len(r["donors"]) for r in rows),
            "lanes": dict(classified)}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify-local-objects", action="store_true")
    args = parser.parse_args()
    with LEDGER.open(encoding="utf-8") as handle:
        report = verify(json.load(handle), verify_local_objects=args.verify_local_objects)
    print("PASS: exact-head, eleven-lane source bridge ledger", report)
    if args.verify_local_objects:
        print("LOCAL git object/readback coverage only; still NO kernel receipt")
    else:
        print("Manifest and status semantics only; exact donor blobs not rechecked locally")
    print("No Clay, Bishop, Karp, BSD, NS, RH, Hodge or world promotion authorized")

if __name__ == "__main__":
    main()
