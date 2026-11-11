#!/usr/bin/env python3
"""Fail-closed handoff from native lean4export v3 to the authoritative DAG validator.

This queues a content-addressed export, NOT an admitted mathematical statement,
validated DAG, or kernel-certified proof. No repository checkout is retained.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re
from pathlib import Path

SHA40 = re.compile(r"[0-9a-f]{40}\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9'.]*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
KINDS = ("thm", "def", "opaque", "axiom", "inductive", "quot", "ctor", "rec")

class AdmissionError(ValueError):
    pass

def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def verify_receipt(receipt: dict, *, max_artifact_bytes: int = 200_000_000) -> tuple[bytes, dict]:
    if not isinstance(receipt, dict) or receipt.get("schema") != "dashi-lean-ephemeral-native-export-v1":
        raise AdmissionError("unsupported native receipt schema")
    if receipt.get("status") != "native-v3-exported-unadmitted":
        raise AdmissionError("native export not in unadmitted state")
    if any(receipt.get(key) is not False for key in
           ("world_admitted", "kernel_proof_certified", "complete_dag_checked")):
        raise AdmissionError("unsupported proof/world promotion")
    repo, revision = receipt.get("repository"), receipt.get("revision")
    if not isinstance(repo, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo):
        raise AdmissionError("invalid repository identity")
    if not isinstance(revision, str) or not SHA40.fullmatch(revision):
        raise AdmissionError("unpinned source revision")
    for field in ("module", "declaration"):
        value = receipt.get(field)
        if not isinstance(value, str) or not MODULE.fullmatch(value):
            raise AdmissionError("invalid " + field)
    if not isinstance(receipt.get("toolchain"), str) or not receipt["toolchain"].strip():
        raise AdmissionError("missing toolchain")
    if not isinstance(receipt.get("dependency_closure_id"), str):
        raise AdmissionError("invalid dependency closure identity")
    sources = receipt.get("source_closure")
    if not isinstance(sources, list) or not sources:
        raise AdmissionError("missing source closure")
    seen = set()
    for src in sources:
        if not isinstance(src, dict):
            raise AdmissionError("invalid source record")
        path, hash_ = src.get("path"), src.get("sha256")
        if (not isinstance(path, str) or not path.endswith(".lean") or
                path.startswith("/") or any(x in ("", ".", "..") for x in path.split("/"))):
            raise AdmissionError("invalid source path")
        if path in seen:
            raise AdmissionError("duplicate source path")
        seen.add(path)
        if not isinstance(hash_, str) or not SHA256.fullmatch(hash_):
            raise AdmissionError("invalid source hash")
    if receipt["module"].replace(".", "/") + ".lean" not in seen:
        raise AdmissionError("exported module absent from source closure")
    reported = receipt.get("artifact_sha256")
    if not isinstance(reported, str) or not SHA256.fullmatch(reported):
        raise AdmissionError("invalid export hash")
    path = receipt.get("artifact_path")
    if not isinstance(path, str):
        raise AdmissionError("missing export artifact")
    artifact = Path(path)
    if artifact.is_symlink() or not artifact.is_file() or artifact.stat().st_size > max_artifact_bytes:
        raise AdmissionError("unsafe or oversized export artifact")
    raw = artifact.read_bytes()
    if not raw or digest(raw) != reported:
        raise AdmissionError("export artifact digest mismatch")
    verification = receipt.get("validation")
    if not isinstance(verification, dict) or verification.get("export_sha256") != reported:
        raise AdmissionError("invalid exporter verification")
    if (verification.get("syntax_v3_checked") is not True or
            verification.get("dag_validated") is not False or
            verification.get("kernel_proof_verified") is not False):
        raise AdmissionError("unexpected validation promotion")
    lines = raw.splitlines()
    if not lines or len(lines) != verification.get("ndjson_records"):
        raise AdmissionError("native record-count mismatch")
    declarations = 0
    for i, line in enumerate(lines):
        if not line or len(line) > 8_000_000:
            raise AdmissionError("invalid native record length")
        try:
            row = json.loads(line)
        except (ValueError, UnicodeError) as exc:
            raise AdmissionError("invalid native NDJSON") from exc
        if not isinstance(row, dict):
            raise AdmissionError("non-object native record")
        if i == 0:
            meta = row.get("meta")
            fmt = meta.get("format") if isinstance(meta, dict) else None
            version = fmt.get("version") if isinstance(fmt, dict) else None
            if not isinstance(version, str) or not version.startswith("3."):
                raise AdmissionError("invalid native v3 metadata")
        elif "meta" in row:
            raise AdmissionError("duplicate native metadata")
        if any(k in row for k in KINDS):
            declarations += 1
    if declarations == 0 or declarations != verification.get("declaration_records"):
        raise AdmissionError("native declaration-count mismatch")
    identity = {
        "schema": "dashi-lean-world-native-handoff-v1",
        "repository": repo, "revision": revision,
        "module": receipt["module"], "declaration": receipt["declaration"],
        "toolchain": receipt["toolchain"],
        "dependency_closure_id": receipt["dependency_closure_id"],
        "source_closure": sorted((s["path"], s["sha256"]) for s in sources),
        "export_sha256": reported, "ndjson_records": len(lines),
        "declaration_records": declarations,
        "status": "pending-authoritative-dag-validation",
        "world_admitted": False, "kernel_proof_certified": False
    }
    return raw, identity

def enqueue(receipt: dict, spool: Path) -> dict:
    raw, record = verify_receipt(receipt)
    spool.mkdir(parents=True, exist_ok=True)
    key = digest(json.dumps(record, sort_keys=True, separators=(",", ":")).encode())
    artifact = spool / (digest(raw) + ".ndjson")
    try:
        with artifact.open("xb") as fd:
            fd.write(raw)
            fd.flush()
            os.fsync(fd.fileno())
    except FileExistsError:
        if artifact.read_bytes() != raw:
            raise AdmissionError("conflicting staged native artifact")
    record["artifact_path"] = str(artifact.resolve())
    manifest = spool / (key + ".json")
    expected = json.dumps(record, sort_keys=True, separators=(",", ":")).encode() + b"\n"
    try:
        with manifest.open("xb") as fd:
            fd.write(expected)
            fd.flush()
            os.fsync(fd.fileno())
    except FileExistsError:
        if manifest.read_bytes() != expected:
            raise AdmissionError("conflicting handoff identity")
    return {"handoff_key": key, "manifest": str(manifest),
            "artifact_path": str(artifact.resolve()),
            "artifact_sha256": digest(raw),
            "status": "pending-authoritative-dag-validation", "world_admitted": False}

def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("receipt_json", type=Path)
    p.add_argument("--spool", type=Path, required=True)
    args = p.parse_args()
    try:
        result = enqueue(json.loads(args.receipt_json.read_text()), args.spool)
    except (AdmissionError, ValueError, OSError) as exc:
        p.exit(2, f"handoff rejected: {exc}\n")
    print(json.dumps(result, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
