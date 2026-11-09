#!/usr/bin/env python3
"""Fail-closed 2019/8575 approved-source intake; never adjudicates authenticity.

Checks actual local bytes against an externally prepared manifest and the
four precise revision labels stated in the signed 16 October 2026 approval.
A manifest, filename, digest or page label alone cannot prove the document
is the one endorsed by the Commonwealth; that needs independent agency
provenance and the actual signed-approval document join.
Only standard Python libraries. No network, macros or PDF parsing.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import tempfile

EXPECTED = {
    "july_pd": "3 July 2026 Issue F",
    "mww_omp": "15 October 2026 9612-E Issue D",
    "esk_omp": "15 October 2026 0102-059 Version 6",
    "avonvale_omp": "15 October 2026 Oes1:v1.2(e)",
}
ALLOWED_KINDS = {"application/pdf", "application/vnd.ms-excel.sheet.macroEnabled.12"}

def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def check(manifest_path: Path) -> dict:
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    artifacts = data.get("artifacts")
    if not isinstance(artifacts, list):
        raise ValueError("artifacts must be a list")
    by_role = {}
    for entry in artifacts:
        role = entry.get("role")
        if not isinstance(role, str) or role in by_role:
            raise ValueError("missing or duplicate artifact role")
        by_role[role] = entry
    results = []
    for role, expected_revision in EXPECTED.items():
        entry = by_role.get(role)
        if entry is None:
            results.append({"role":role,"status":"MISSING", "expected_revision":expected_revision})
            continue
        p = (manifest_path.parent / entry.get("path","")).resolve()
        # A download listing without local bytes is NOT a received source.
        if not p.is_file():
            results.append({"role":role,"status":"NO_BYTES","expected_revision":expected_revision})
            continue
        claimed = entry.get("sha256")
        matched = isinstance(claimed,str) and len(claimed)==64 and all(c in "0123456789abcdef" for c in claimed)
        actual = digest(p)
        revision_ok = entry.get("claimed_revision") == expected_revision
        receipt = entry.get("original_agency_acceptance_receipt")
        has_receipt = isinstance(receipt,str) and bool(receipt.strip())
        results.append({
            "role":role,
            "status":"HASH_VERIFIED_VERSION_CLAIM_ONLY" if matched and claimed==actual and revision_ok else "FAILED",
            "expected_revision":expected_revision,
            "sha256":actual,
            "revision_claim_matches":revision_ok,
            "separate_original_agency_acceptance_receipt_supplied":has_receipt,
            "original_agency_acceptance_independently_authenticated":False,
        })
    return {
        "case":"EPBC 2019/8575",
        "bytes_and_claims_pass":all(r["status"]=="HASH_VERIFIED_VERSION_CLAIM_ONLY" for r in results),
        "approved_originals_authenticity_established":False,
        "accepted_OAG_workbook_cells_or_formulas_verified":False,
        "results":results,
        "method":"hash/revision consistency only; never equates filename/manifest text with official approval",
    }

def selftest():
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        entries=[]
        for role,version in EXPECTED.items():
            p=root/(role+".pdf")
            p.write_bytes(("FIXTURE-"+role).encode())
            entries.append({"role":role,"path":p.name,"sha256":digest(p),
                            "claimed_revision":version,
                            "original_agency_acceptance_receipt":""})
        manifest=root/"sources.json"
        manifest.write_text(json.dumps({"artifacts":entries}))
        good=check(manifest)
        assert good["bytes_and_claims_pass"]
        assert not good["approved_originals_authenticity_established"]
        entries[0]["sha256"]="0"*64
        manifest.write_text(json.dumps({"artifacts":entries}))
        bad=check(manifest)
        assert not bad["bytes_and_claims_pass"]
        entries[0]["sha256"]=digest(root/"july_pd.pdf")
        entries[1]["claimed_revision"]="January 2026 substitute"
        manifest.write_text(json.dumps({"artifacts":entries}))
        wrong=check(manifest)
        assert not wrong["bytes_and_claims_pass"]
        entries.pop()
        manifest.write_text(json.dumps({"artifacts":entries}))
        missing=check(manifest)
        assert not missing["bytes_and_claims_pass"]
    return {"tests":4,"passed":4,"synthetic_fixtures_only":True,
            "authentic_case_originals_obtained":False}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--manifest",type=Path)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if args.self_test:
        print(json.dumps(selftest(),indent=2))
    elif args.manifest:
        print(json.dumps(check(args.manifest),indent=2))
    else:
        parser.error("provide --self-test or --manifest")

if __name__=="__main__":
    main()
