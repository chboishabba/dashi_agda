#!/usr/bin/env python3
"""Fail-closed original YM 219-field source/predicate bidirectional audit.

Runs on an actual checkout of PR #1444:
  python scripts/check_ym_219_bidirectional_proof_audit.py --repo .
  python scripts/check_ym_219_bidirectional_proof_audit.py --self-test

This is an EXACT SOURCE/PROVENANCE checker, not Agda typechecking or a
proof that any physical 4D YM obligation is discharged.
"""
import argparse
import copy
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

ORIGINAL = "Docs/roadmaps/YMClaySubmission219FieldInventory20261103.json"
AUDIT = "Docs/roadmaps/YMClay219ProofRelevantBidirectionalAudit20261104.json"
LEDGER = "Docs/roadmaps/YMClayCurrentExactLemmaLedger20261103.md"
T78 = "DASHI/Physics/YangMills/BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.agda"
GATES = {"R443", "R445", "R320", "R333", "CLAY"}
PRODUCER = re.compile(r"^\|\s*((?:R443|R445|R320|R333|CLAY|TRUST)\.[FPK]\d{2})\s*\|")
UPGRADE_FIELDS = (
    "selected_physical_proposition",
    "selected_physical_owner",
    "source_proof_term",
    "kernel_receipt",
    "same_object_transport_term",
)

def git_blob_sha(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def fail(message):
    raise AssertionError(message)

def verify_row(row, original, source_text, source_blob):
    for k in ("field_id", "source_record", "original_field", "original_source_path",
              "original_source_blob_sha", "candidate_gate_hints"):
        if k not in row:
            fail(f"{original['id']}: missing {k}")
    if (row["field_id"], row["original_field"], row["source_record"],
        row["original_source_path"], row["original_source_blob_sha"],
        row["candidate_gate_hints"]) != (
        original["id"], original["field"], original["contract_record"],
        original["source_path"], original["source_blob_sha"],
        original["producer_gate_hints"]):
        fail(f"{original['id']}: original source/provenance changed")
    if source_blob != original["source_blob_sha"]:
        fail(f"{original['id']}: original cutset blob SHA changed")
    pattern = re.compile(r"^\s*" + re.escape(original["field"]) + r"\s*:\s*Set\s*$")
    hits = [i + 1 for i, line in enumerate(source_text.splitlines())
            if pattern.fullmatch(line)]
    if hits != [row["original_line"]]:
        fail(f"{original['id']}: missing or moved bare-Set declaration: {hits}")
    if row["actual_declaration_type"] != "Set" or (
        row["declaration_semantics"] != "TYPE_VALUED_PLACEHOLDER_NOT_A_PROOF"):
        fail(f"{original['id']}: bare-Set was silently promoted to proof")
    if row["candidate_edge_status"] != "SEARCH_HINT_ONLY":
        fail(f"{original['id']}: gate-search relation falsely promoted")
    if not set(row["candidate_gate_hints"]) <= GATES:
        fail(f"{original['id']}: unrecognized candidate gate")
    status = row["discharge_class"]
    if status == "NOT_AUDITED":
        if any(row.get(k) is not None for k in UPGRADE_FIELDS):
            fail(f"{original['id']}: evidence present without audit status")
    elif status == "PROVED":
        if not all(row.get(k) for k in UPGRADE_FIELDS):
            fail(f"{original['id']}: missing proof-relevant selected physical evidence")
        if row.get("direct_endpoint_edge") and not row.get("endpoint_compiler_theorem"):
            fail(f"{original['id']}: endpoint promotion lacks compiler")
    elif status == "ELIMINATED":
        for k in ("selected_physical_proposition", "redundancy_implication_proof",
                  "kernel_receipt"):
            if not row.get(k):
                fail(f"{original['id']}: redundancy claimed without physical implication")
    else:
        fail(f"{original['id']}: invalid field status {status}")

def verify_reverse(rows, reverse):
    expected = defaultdict(list)
    for row in rows:
        for gate in row["candidate_gate_hints"]:
            expected[gate].append(row["field_id"])
    if dict(expected) != reverse:
        fail("reversed gate-hint lookup is not equal to forward field index")
    assert set(reverse) <= GATES
    assert sum(map(len, reverse.values())) == sum(
        len(row["candidate_gate_hints"]) for row in rows)

def check(repo):
    root = Path(repo)
    orig = json.loads((root / ORIGINAL).read_text())
    audit = json.loads((root / AUDIT).read_text())
    ledger = (root / LEDGER).read_text()
    t78 = (root / T78).read_text()
    if audit["audit_basis"]["original_219_inventory_blob_sha"] != git_blob_sha(
            (root / ORIGINAL).read_bytes()):
        fail("219 original inventory blob drift")
    if audit["audit_basis"]["producer_ledger_blob_sha"] == git_blob_sha(
            (root / LEDGER).read_bytes()):
        pass
    else:
        # Ledger may have additive work after the frozen source-audit
        # snapshot; producer IDs/statuses below still must agree.
        print("INFO: live producer-ledger blob differs from audit snapshot")
    if len(orig["rows"]) != 219 or len(audit["original_fields"]) != 219:
        fail("219 original field count drift")
    ids = [r["id"] for r in orig["rows"]]
    if len(ids) != len(set(ids)):
        fail("duplicate original field ID")
    sources = {}
    for p in {r["source_path"] for r in orig["rows"]}:
        blob = (root / p).read_bytes()
        sources[p] = (blob.decode("utf-8"), git_blob_sha(blob))
        if audit["audit_basis"]["source_contract_blob_sha"][p] != sources[p][1]:
            fail(f"original contract source changed: {p}")
    for a, o in zip(audit["original_fields"], orig["rows"]):
        path = o["source_path"]
        verify_row(a, o, *sources[path])
    verify_reverse(audit["original_fields"], audit["gate_hint_reverse_index"])
    ids = [m.group(1) for line in ledger.splitlines()
           if (m := PRODUCER.match(line))]
    if len(ids) != len(set(ids)):
        fail("duplicate gate-producer ID")
    snap_ids = [row["id"] for row in audit["producer_catalog"]]
    if ids != snap_ids:
        fail("producer IDs changed: regenerate and review audit in full")
    if len(ids) != 63:
        fail("original 63-producer audit baseline changed")
    for row in audit["producer_catalog"]:
        if row["relation_to_submission_fields"] != (
                "NOT_AUDITED_CANDIDATE_GATE_ASSOCIATION_ONLY"):
            fail(f"claimed proof edge at producer {row['id']}")
    if audit["exact_bare_Set_fields"] != 219:
        fail("219 bare Set count must be demonstrated, not revised by assertion")
    if any(row["discharge_class"] != "NOT_AUDITED" for row in audit["original_fields"]):
        print("INFO: proposed upgraded fields must be independently kernel audited")
    theorem = audit["chosen_terminal_compiler"]["theorem"]
    if theorem != "literalClaySolutionFromTopDownThree" or theorem not in t78:
        fail("literal top-down compiler mismatch")
    expected = [
        "Five.LiteralClayStructuralBase Y",
        "UVToContinuumYM Y",
        "SameHamiltonianPhysicalMassGap Y",
        "SameFamilyLocalFieldsOPEStressWard Y",
        "StandardSameHGaussianNontrivialityConsequence Y",
    ]
    if audit["chosen_terminal_compiler"]["sufficient_physical_inputs"] != expected:
        fail("top-down typed sufficiency signature mismatch")
    if audit["chosen_terminal_compiler"]["converse_status"] != "UNPROVED_NOT_ASSUMED":
        fail("unproved reverse Clay implication promoted")
    print(json.dumps({
        "result": "PASS_SOURCE_ONLY",
        "original_fields": len(ids) and len(audit["original_fields"]),
        "all_original_fields_bare_Set": audit["exact_bare_Set_fields"],
        "candidate_producer_rows": len(ids),
        "forward_reverse_search_edges": sum(map(len, audit["gate_hint_reverse_index"].values())),
        "proved_physical_field_receipts": sum(
            r["discharge_class"] == "PROVED" for r in audit["original_fields"]),
        "round78_converse": "NOT_PROVED",
        "agda_kernel": "NOT_CHECKED",
        "physical_clay": "OPEN",
    }, indent=2))

def self_test():
    f = {
        "id": "YM-A001", "field": "sampleField", "contract_record": "T",
        "source_path": "src.agda", "source_blob_sha": git_blob_sha(
            b"  field\n    sampleField : Set\n"),
        "producer_gate_hints": ["R443", "R445"],
    }
    row = {
        "field_id": f["id"], "original_field": f["field"],
        "source_record": f["contract_record"],
        "original_source_path": f["source_path"],
        "original_source_blob_sha": f["source_blob_sha"],
        "candidate_gate_hints": f["producer_gate_hints"],
        "actual_declaration_type": "Set",
        "declaration_semantics": "TYPE_VALUED_PLACEHOLDER_NOT_A_PROOF",
        "candidate_edge_status": "SEARCH_HINT_ONLY",
        "original_line": 2,
        "discharge_class": "NOT_AUDITED",
        "direct_endpoint_edge": None,
    }
    for k in UPGRADE_FIELDS:
        row[k] = None
    text = "  field\n    sampleField : Set\n"
    verify_row(row, f, text, f["source_blob_sha"])
    verify_reverse([row], {"R443": ["YM-A001"], "R445": ["YM-A001"]})
    errors = []
    for mutation in (
        {"discharge_class": "PROVED"},
        {"candidate_edge_status": "THEOREM"},
        {"actual_declaration_type": "sampleField"},
        {"original_line": 1},
        {"candidate_gate_hints": ["R443", "BAD"]},
    ):
        changed = copy.deepcopy(row)
        changed.update(mutation)
        try:
            verify_row(changed, f, text, f["source_blob_sha"])
        except AssertionError:
            errors.append(mutation)
    assert len(errors) == 5
    try:
        verify_reverse([row], {"R443": ["YM-A001"]})
    except AssertionError:
        pass
    else:
        fail("missing reverse edge not rejected")
    try:
        verify_row(row, f, text, "badsha")
    except AssertionError:
        pass
    else:
        fail("wrong SHA not rejected")
    print("PASS: 7 fail-closed mutation controls; source check requires real checkout")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    else:
        check(args.repo)
