#!/usr/bin/env python3
"""Acquire Wang et al. (2019) human geomagnetic EEG originals, fail closed.

Original paper DOI: 10.1523/ENEURO.0483-18.2019.
Data custodian: Joseph L. Kirschvink, CaltechDATA D1.930 / D1.931.
Original licence and privacy rules remain in force. Do not commit .mat files.
This does NOT compute original EEG effects.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import urllib.error
import urllib.request

RECORDS = {
    "declination": ("qyhmj-96g11", "10.22002/D1.930", {
        "analyzeDecDn.m": "a9edb02840112e7b375a43ea116cb94b",
        "analyzeDecTest.m": "7570e3b33e255bb048cc20505a5b6fb9",
        "DecDn.Data.01.mat": "93028ab6077e64e6ed92344a90aad472",
    }),
    "inclination": ("fx074-jee09", "10.22002/D1.931", {
        "analyzeIncTest.m": "43e334036fe79ad0671991d5899a8949",
        "Inc.Data.01.mat": "15305bea702a5e5702575d67da2d1c63",
    }),
}


def plan(include_subject=False):
    out = []
    for group, (record, doi, files) in RECORDS.items():
        for name, md5 in files.items():
            if name.endswith(".mat") and not include_subject:
                continue
            out.append({"group": group, "filename": name, "doi": doi,
                        "record": record, "md5_expected": md5,
                        "source_url": f"https://data.caltech.edu/records/{record}/files/{name}?download=1"})
    return out


def hash_file(path):
    md5, sha, count = hashlib.md5(), hashlib.sha256(), 0
    with path.open("rb") as fh:
        for part in iter(lambda: fh.read(1024 * 1024), b""):
            md5.update(part)
            sha.update(part)
            count += len(part)
    return {"md5": md5.hexdigest(), "sha256": sha.hexdigest(), "size_bytes": count}


def acquire(item, root, timeout):
    dest = root / item["group"] / item["filename"]
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        observed = hash_file(dest)
        if observed["md5"] != item["md5_expected"]:
            raise ValueError(f"Existing file differs from published hash: {dest}")
        return {**item, "status": "verified-existing", **observed}
    tmp = dest.with_suffix(dest.suffix + ".part")
    req = urllib.request.Request(item["source_url"], headers={
        "User-Agent": "DASHI-Source-Integrity-Research/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as response, tmp.open("wb") as out:
            if "text/html" in response.headers.get("Content-Type", "").lower():
                raise ValueError("HTML returned rather than original file")
            while True:
                part = response.read(1024 * 1024)
                if not part:
                    break
                out.write(part)
        result = hash_file(tmp)
        if result["md5"] != item["md5_expected"]:
            raise ValueError(f"MD5 mismatch for {item['filename']}: {result['md5']}")
        os.replace(tmp, dest)
        return {**item, "status": "verified-downloaded", **result}
    finally:
        if tmp.exists():
            tmp.unlink()


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out", type=Path, default=Path("./radiobio-original-data"))
    p.add_argument("--one-subject", action="store_true",
                   help="include one DecDn and one Inc .mat file; ~110MB additional")
    p.add_argument("--download", action="store_true",
                   help="actually retrieve; default only outputs provenance plan")
    p.add_argument("--timeout", type=int, default=60)
    args = p.parse_args(argv)
    files = plan(args.one_subject)
    if not args.download:
        print(json.dumps({"status": "PLAN_ONLY_NO_NETWORK", "files": files}, indent=2))
        return 0
    args.out.mkdir(parents=True, exist_ok=True)
    receipts = []
    for item in files:
        try:
            receipts.append(acquire(item, args.out, args.timeout))
        except (OSError, urllib.error.URLError, ValueError) as e:
            receipts.append({**item, "status": "FAILED_NO_ORIGINAL_BYTES",
                             "error_type": type(e).__name__, "error": str(e)[:400]})
    result = {
        "authors": "Wang et al. (2019); Joseph L. Kirschvink (CaltechDATA)",
        "is_original_eeg_replay": False,
        "all_bytes_verified": all(r["status"].startswith("verified") for r in receipts),
        "entries": receipts,
    }
    (args.out / "acquisition_receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return 0 if result["all_bytes_verified"] else 2


if __name__ == "__main__":
    sys.exit(main())
