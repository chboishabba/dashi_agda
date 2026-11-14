#!/usr/bin/env python3
"""DASHI fail-closed external OpenAI Yang--Mills source admission.

Metadata-only validation NEVER checks a theorem. Full --upstream/--review mode
checks Git blob bytes against two pinned PUBLIC repository snapshots.
Git SHA1 here is a content identity, not an axiom, kernel or theorem check.
"""
import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path

MANIFEST = Path(__file__).resolve().parents[1] / "Docs/roadmaps/OpenAIYangMills2026ProofIngest20261114.json"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
EXPECTED = {"A1", "A2", "A3", "A4", "A5", "A6", "A7", "A8"}
BANNED = {"dashi_agda_kernel_accepted", "dashi_lean_kernel_accepted",
          "world_ingest_accepted", "dashi_e1_original_wilson_same_object",
          "dashi_d1_continuum_decay", "dashi_d2_same_hamiltonian_gap",
          "clay_ym_solved", "unique_infinite_volume_limit", "confinement",
          "all_orders_msbar"}

def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + bytes([0]) + data).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def validate(m):
    require(m.get("schema") == "dashi-oai-ym-proof-intake-v1", "wrong manifest schema")
    for name, ref in (("upstream", "3456e5e75cf8d4cd558955a5c7638fba2d68f464"),
                      ("review", "55ba9fc36293b3f4d52c6b1f813169a0be76ee98")):
        x = m.get(name)
        require(isinstance(x, dict) and x.get("commit") == ref, f"unpinned {name}")
        expected_repo = ("yang-mills-group/OpenAI-YM-20261028" if name == "upstream"
                         else "yang-mills-group/YM")
        require(x.get("repository") == expected_repo, f"wrong {name} repository")
        if name == "upstream":
            require(x.get("lean_toolchain") == "leanprover/lean4:v4.32.0",
                    "unpinned source Lean version")
        require(HEX40.fullmatch(x["commit"]) is not None, "invalid SHA")
        require(len(x.get("files", [])) > 0, f"missing {name} file inventory")
        paths = set()
        for entry in x["files"]:
            p = entry["path"]
            require(isinstance(p, str) and p not in paths and
                    not p.startswith("/") and ".." not in Path(p).parts,
                    f"unsafe or duplicate path: {p}")
            require(HEX40.fullmatch(entry["git_blob"]) is not None,
                    f"invalid Git blob for {p}")
            paths.add(p)
    assert_fields = m.get("prohibited_promotions", {})
    require(set(assert_fields) == BANNED, "promotion firewall fields changed")
    require(all(v is False for v in assert_fields.values()),
            "attempted mathematical or kernel promotion")
    clauses = m.get("clauses", [])
    require({c.get("id") for c in clauses} == EXPECTED and len(clauses) == 8,
            "review A1--A8 inventory must be exact")
    require(all(c.get("status") in {
        "unmatched", "not_same_source_proved",
        "external_reviewed_not_transported", "separate_witness_not_joined"}
        for c in clauses), "unsupported same-object declaration")
    require(m["dashi_owner"]["bridge_status"] == "SOURCE_ONLY_NO_FORMAL_CROSS_KERNEL_IMPORT",
            "unearned proof-transport status")
    require(m["existing_openai_math_corpus"]["same_corpus_as_yang_mills"] is False,
            "original openai/math corpus and Oct YM source wrongly conflated")
    return True

def verify_bytes(files, base):
    verified = []
    for item in files:
        target = base / item["path"]
        require(not target.is_symlink() and target.is_file(),
                f"missing/unsafe pinned source {target}")
        actual = git_blob(target.read_bytes())
        require(actual == item["git_blob"], f"source-byte drift {target}")
        verified.append(item["path"])
    return verified

def selftest(m):
    import tempfile
    validate(m)
    for mutation in ("gap", "missing", "status", "corpus"):
        changed = copy.deepcopy(m)
        if mutation == "gap":
            changed["prohibited_promotions"]["clay_ym_solved"] = True
        elif mutation == "missing":
            changed["clauses"].pop()
        elif mutation == "status":
            changed["clauses"][0]["status"] = "kernel_accepted"
        else:
            changed["existing_openai_math_corpus"]["same_corpus_as_yang_mills"] = True
        try:
            validate(changed)
        except ValueError:
            continue
        raise AssertionError(f"negative control incorrectly accepted: {mutation}")
    with tempfile.TemporaryDirectory() as tmp:
        base = Path(tmp)
        (base / "proof.lean").write_bytes(b"theorem good : True := True.intro\\n")
        blob = git_blob((base / "proof.lean").read_bytes())
        verify_bytes([{"path":"proof.lean", "git_blob":blob}], base)
        (base / "proof.lean").write_bytes(b"theorem good : False := by sorry\\n")
        try:
            verify_bytes([{"path":"proof.lean","git_blob":blob}], base)
        except ValueError:
            pass
        else:
            raise AssertionError("modified proof bytes admitted")
    return 6

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--manifest", type=Path, default=MANIFEST)
    p.add_argument("--upstream", type=Path, help="checkout root of OpenAI-YM-20261028")
    p.add_argument("--review", type=Path, help="checkout root of yang-mills-group/YM")
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    m = json.loads(args.manifest.read_text(encoding="utf-8"))
    validate(m)
    tests = selftest(m) if args.self_test else 0
    require((args.upstream is None) == (args.review is None),
            "both source trees required for byte-admission")
    verified = []
    if args.upstream is not None:
        verified += verify_bytes(m["upstream"]["files"], args.upstream)
        verified += verify_bytes(m["review"]["files"], args.review)
    print(json.dumps({"schema":m["schema"],"result":"PASS",
        "metadata_valid":True,"negative_controls":tests,
        "source_bytes_verified":len(verified),
        "native_kernel_checked":False,"same_object_transport_paid":False,
        "clay_promoted":False},indent=2))
if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, AssertionError) as e:
        print(f"FAIL_CLOSED: {e}",file=sys.stderr)
        sys.exit(1)
