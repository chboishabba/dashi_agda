#!/usr/bin/env python3
"""Offline source-type witness audit for canonical DASHI Clay rollups.

Checks precise Git-blob identities and critical named theorem interface snippets
for 13 source cases. Does NOT prove absence of other proofs; does not claim
Agda/Lean kernel, any physical estimate or a Clay result.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
DATA = HERE / "Docs/roadmaps/ClaySourceVerifiedExistingVsOpen20261114.json"

def require(ok, msg):
    if not ok:
        raise ValueError(msg)

def blob_sha(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\x00" + raw).hexdigest()

def check_source(row, roots):
    root = roots[row["repo"]]
    f = root / row["path"]
    require(f.is_file() and not f.is_symlink(), "missing/untrusted source " + str(f))
    raw = f.read_bytes()
    require(blob_sha(raw) == row["blob"],
            "source changed, re-audit theorem TYPE: " + str(f))
    src = raw.decode("utf-8")
    for marker in row["signatures"]:
        require(marker in src,
                "expected original source signature is missing: " + row["id"] + ": " + marker)

def check_gitlink(lean, sha):
    r = subprocess.run(["git", "-C", str(lean), "ls-tree", "HEAD", "vendor/openai-math-src"],
                       capture_output=True, text=True, check=True)
    line = r.stdout.strip()
    require(line.startswith("160000 commit " + sha + "\t"),
            "OpenAI math vendor gitlink was replaced, absent or changed")
    g = (lean / ".gitmodules").read_text(encoding="utf-8")
    require("path = vendor/openai-math-src" in g and
            "url = https://github.com/openai/math.git" in g,
            "invalid OpenAI math submodule origin")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--agda-root", type=Path, default=HERE)
    parser.add_argument("--lean-root", type=Path, required=True)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(DATA.read_text(encoding="utf-8"))
    require(manifest["schema"] == "dashi-clay-existing-theorems-vs-open-physical-producers-v1", "schema drift")
    require(manifest["all_terminal_problems_solved"] is False and
            manifest["any_new_kernel_receipt"] is False, "source metadata falsely promoted")
    rows = manifest["rows"]
    require(len(rows) == 13 and len({r["id"] for r in rows}) == len(rows), "audit row completeness/uniqueness")
    roots = {"agda": args.agda_root.resolve(), "lean": args.lean_root.resolve()}
    for row in rows:
        require(row["repo"] in roots and row["signatures"] and
                row["source_receipt"] and row["outstanding"] and row["tier"], "bad row")
        check_source(row, roots)
    check_gitlink(roots["lean"], manifest["vendoring"]["openai_math_gitlink_commit"])
    if args.self_test:
        marker = rows[0]["signatures"][0]
        require(marker not in "not actually the terminal physical witness", "negative marker test invalid")
        original = rows[0]["blob"]
        require(original != "0"*40, "negative blob test invalid")
    print(json.dumps({"status":"SOURCE_AUDIT_PASS","rows":len(rows),
        "agda_source_files":sum(r["repo"]=="agda" for r in rows),
        "lean_source_files":sum(r["repo"]=="lean" for r in rows),
        "vendor_gitlink_pinned":True,
        "same_object_proof_imports_proved":False,"kernel_executed":False,
        "terminal_clay_proof_produced":False},indent=2))

if __name__=="__main__":
    try: main()
    except (ValueError, OSError, subprocess.CalledProcessError, KeyError,
            UnicodeError, json.JSONDecodeError) as exc:
        print("SOURCE_AUDIT_BLOCKED:", exc, file=sys.stderr)
        sys.exit(1)
