#!/usr/bin/env python3
"""Fail-closed pinned donor/recipient byte-identity audit for Bishop eta sources.

Default validates the immutable manifest and keeps all analytic/kernel gates OPEN.
--verify-local-objects additionally verifies ten Git blob identities, the
recipient's 31 actual immediate DASHI imports, and the new same-term owner.
It never fetches, merges, invokes CI, or pretends to typecheck Agda.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = ROOT / "Docs/roadmaps/BishopEtaCrossPRSourceTransferReceipt20261113.json"
SHA = re.compile(r"[0-9a-f]{40}\Z")
PATH = re.compile(r"DASHI/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.agda\Z")
IMPORT = re.compile(
    r"^\s*(?:open\s+)?import\s+(DASHI(?:\.[A-Za-z0-9_]+)+)",
    flags=re.MULTILINE,
)

class Blocked(RuntimeError):
    pass

def require(ok, description):
    if not ok:
        raise Blocked(description)

def git(repo, *args, text=True):
    result = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True,
        text=text, check=False,
    )
    require(result.returncode == 0, "missing/invalid local git object: " +
            " ".join(args))
    return result.stdout.strip() if text else result.stdout

def verify_receipt(doc, *, verify_local_objects=False, root=ROOT):
    require(doc.get("repository") == "chboishabba/dashi_agda",
            "unexpected repository")
    require(doc.get("source_pr") == 1408 and doc.get("recipient_pr") == 1478,
            "wrong original donor/recipient")
    source, recipient = doc.get("source_head"), doc.get("recipient_head")
    require(isinstance(source, str) and SHA.fullmatch(source),
            "donor not SHA-pinned")
    require(isinstance(recipient, str) and SHA.fullmatch(recipient),
            "recipient not SHA-pinned")
    require(source != recipient, "donor/recipient accidentally collapsed")
    require(doc.get("source_status") ==
            "same_branch_byte_identical_eta_sources_and_native_exp_source_not_typechecked",
            "source status misclassified")
    for flag in ("local_agda29_kernel_accepted", "all_imports_elaborated",
                 "original_dyadic_term_identity_proved",
                 "compact_uniform_eta_convergence_proved",
                 "clay_or_rh_theorem_proved"):
        require(doc.get(flag) is False,
                "unauthorized mathematical/kernel promotion: " + flag)

    files = doc.get("copied_source_blobs")
    require(isinstance(files, list) and len(files) == 10,
            "expected exactly ten transfer blobs")
    paths = [x.get("path") for x in files]
    require(len(set(paths)) == 10 and all(
        isinstance(p, str) and PATH.fullmatch(p) for p in paths),
        "invalid/duplicate original Agda transplant file")
    require(all(isinstance(x.get("blob_sha"), str) and
                SHA.fullmatch(x["blob_sha"]) for x in files),
            "missing immutable donor blob hashes")
    require("DASHI/Analysis/BishopOriginalEtaEvenSourceScaleFiniteWeldExact.agda"
            in paths, "real eta scaling owner missing")

    deps = doc.get("other_immediate_dashi_imports_present")
    require(isinstance(deps, list) and len(deps) == 31,
            "expected 31 imported original DASHI modules")
    require(len(set(deps)) == 31 and all(isinstance(p, str) and
                PATH.fullmatch(p) and p not in paths for p in deps),
            "import list invalid or overlaps transferred blobs")
    new_owner = doc.get("new_same_term_owner")
    require(new_owner ==
            "DASHI/Analysis/BishopOriginalEtaNativeFactorialExpSourceWeldExact.agda",
            "missing cross-source term owner")

    if verify_local_objects:
        for head in (source, recipient):
            git(root, "cat-file", "-e", head + "^{commit}")

        discovered = set()
        for item in files:
            p, expected = item["path"], item["blob_sha"]
            donor_hash = git(root, "rev-parse", source + ":" + p)
            receiver_hash = git(root, "rev-parse", recipient + ":" + p)
            require(donor_hash == expected and receiver_hash == expected,
                    "donor/receiver blob mismatch: " + p)
            original = git(root, "show", recipient + ":" + p)
            discovered.update(m.replace(".", "/") + ".agda"
                              for m in IMPORT.findall(original))
        discovered.difference_update(paths)
        require(discovered == set(deps),
                "literal source import list drift: missing=" +
                repr(sorted(discovered - set(deps))) + ", stale=" +
                repr(sorted(set(deps) - discovered)))
        for p in deps:
            git(root, "cat-file", "-e", recipient + ":" + p)
        term_source = git(root, "show", recipient + ":" + new_owner)
        for real_import in (
            "DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact",
            "DASHI.Analysis.BishopRiemannDirichletExponentialTermExact",
            "DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact",
        ):
            require(real_import in IMPORT.findall(term_source),
                    "same-term source missing exact owner import: " + real_import)

    return {
        "source": source, "recipient": recipient,
        "copied_source_blobs": len(files),
        "immediate_dashi_imports": len(deps),
        "kernel_accepted": False, "dyadic_identity": False,
        "eta_compact_uniform_convergence": False,
        "local_objects_checked": verify_local_objects,
    }

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--verify-local-objects", action="store_true")
    args = parser.parse_args()
    try:
        doc = json.loads(RECEIPT.read_text(encoding="utf-8"))
        result = verify_receipt(doc, verify_local_objects=
                                args.verify_local_objects, root=args.repo)
    except (Blocked, OSError, ValueError) as ex:
        parser.exit(2, "BLOCKED: " + str(ex) + "\n")
    print("PASS: exact-head Bishop eta donor transfer receipt", result)
    if not args.verify_local_objects:
        print("Manifest semantics only; local Git blob replay NOT RUN.")
    print("No Agda/Lean kernel, original dyadic identity, eta convergence or RH receipt.")

if __name__ == "__main__":
    main()
