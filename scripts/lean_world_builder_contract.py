#!/usr/bin/env python3
"""Fail-closed contract between #1494's queue and an external authoritative DAG builder.

This is NOT a Lean parser, verifier, certification service, or world writer.
No claimed DAG validation can originate in this adapter.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from typing import Protocol
import json
import re

class ContractError(ValueError):
    pass

@dataclass(frozen=True)
class PendingExport:
    handoff_key: str
    artifact_sha256: str
    artifact: bytes
    repository: str
    revision: str
    module: str
    declaration: str
    toolchain: str
    dependency_closure_id: str
    source_closure: tuple

@dataclass(frozen=True)
class BuilderResult:
    handoff_key: str
    artifact_sha256: str
    builder_id: str
    checker_receipt_sha256: str
    node_ids: tuple[str, ...]
    edges: tuple[tuple[str, str], ...]
    dag_validated: bool
    kernel_certified: bool

class AuthoritativeBuilder(Protocol):
    def validate(self, export: PendingExport) -> BuilderResult: ...

HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")

def pending_from_manifest(manifest_path: Path, *, limit=200_000_000) -> PendingExport:
    """Inspect immutable handoff identity and staged bytes; no world mutation."""
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise ContractError("unsafe manifest")
    try:
        m = json.loads(manifest_path.read_bytes())
    except (OSError, ValueError, UnicodeError) as exc:
        raise ContractError("unreadable manifest") from exc
    if not isinstance(m, dict) or m.get("schema") != "dashi-lean-world-native-handoff-v1":
        raise ContractError("unsupported manifest schema")
    if (m.get("status") != "pending-authoritative-dag-validation"
        or m.get("world_admitted") is not False
        or m.get("kernel_proof_certified") is not False):
        raise ContractError("already promoted or invalid admission status")
    for k in ("repository", "revision", "module", "declaration",
              "toolchain", "export_sha256", "artifact_path"):
        if not isinstance(m.get(k), str) or not m[k]:
            raise ContractError("missing " + k)
    if not HEX40.fullmatch(m["revision"]) or not HEX64.fullmatch(m["export_sha256"]):
        raise ContractError("invalid immutable identity")
    if not isinstance(m.get("dependency_closure_id"), str):
        raise ContractError("invalid dependency closure ID")
    source = m.get("source_closure")
    if (not isinstance(source, list) or not source
        or any(not isinstance(s, list) or len(s) != 2
               or not isinstance(s[0], str) or not s[0]
               or not isinstance(s[1], str) or not HEX64.fullmatch(s[1])
               for s in source)):
        raise ContractError("invalid source closure")
    if len({s[0] for s in source}) != len(source):
        raise ContractError("duplicate source")
    for k in ("ndjson_records", "declaration_records"):
        if type(m.get(k)) is not int or m[k] <= 0:
            raise ContractError("invalid record count")
    artifact = Path(m["artifact_path"])
    if (artifact.is_symlink() or not artifact.is_file()
        or artifact.parent.resolve() != manifest_path.parent.resolve()
        or artifact.name != m["export_sha256"] + ".ndjson"
        or artifact.stat().st_size > limit):
        raise ContractError("unsafe native artifact")
    raw = artifact.read_bytes()
    if not raw or sha256(raw).hexdigest() != m["export_sha256"]:
        raise ContractError("native artifact hash mismatch")
    if len(raw.splitlines()) != m["ndjson_records"]:
        raise ContractError("native record count mismatch")
    identity = {k: v for k, v in m.items() if k != "artifact_path"}
    key = sha256(json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    if manifest_path.name != key + ".json":
        raise ContractError("handoff key mismatch")
    return PendingExport(key, m["export_sha256"], raw, m["repository"],
                         m["revision"], m["module"], m["declaration"],
                         m["toolchain"], m["dependency_closure_id"],
                         tuple(tuple(s) for s in source))

def validate_through_builder(export: PendingExport, builder: AuthoritativeBuilder) -> BuilderResult:
    """Only a shape/binding check of external builder output; NOT certification."""
    outcome = builder.validate(export)
    if not isinstance(outcome, BuilderResult):
        raise ContractError("builder did not return an explicit result")
    if (outcome.handoff_key != export.handoff_key
        or outcome.artifact_sha256 != export.artifact_sha256
        or not outcome.builder_id
        or not isinstance(outcome.checker_receipt_sha256, str)
        or not HEX64.fullmatch(outcome.checker_receipt_sha256)
        or outcome.dag_validated is not True
        or outcome.kernel_certified is not False):
        raise ContractError("unbound or incomplete validator evidence")
    ids = outcome.node_ids
    if not ids or len(set(ids)) != len(ids) or any(not isinstance(x, str) or not x for x in ids):
        raise ContractError("invalid canonical node set")
    if any(not isinstance(e, tuple) or len(e) != 2 or e[0] not in ids or e[1] not in ids
           for e in outcome.edges):
        raise ContractError("unresolved dependency reference")
    # Structural DAG sanity is necessary but never sufficient for Lean typing.
    # Process iteratively to avoid recursion-limit failures on untrusted graphs.
    successors = {node: [] for node in ids}
    indegree = {node: 0 for node in ids}
    seen_edges = set()
    for origin, target in outcome.edges:
        if (origin, target) in seen_edges:
            raise ContractError("duplicate dependency edge")
        seen_edges.add((origin, target))
        successors[origin].append(target)
        indegree[target] += 1
    ready = [node for node, degree in indegree.items() if degree == 0]
    visited = 0
    while ready:
        node = ready.pop()
        visited += 1
        for target in successors[node]:
            indegree[target] -= 1
            if indegree[target] == 0:
                ready.append(target)
    if visited != len(ids):
        raise ContractError("cyclic dependency graph")
    # Fake builder claims cannot upgrade a proof. Authenticate the external validator independently.
    # This result never changes a queued manifest or authorizes world admission.
    return outcome
