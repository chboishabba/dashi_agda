#!/usr/bin/env python3
"""Same-export join for #1494/#1495 native projection, Rust checker and #1484 JMD.

This is an OBSERVATION ONLY. A JSON checker receipt is not an authenticated
checker run; a JMD structural projection is not a proof of Lean typing.
No DAG admission, PostgreSQL write, proof status or theorem equality follows.
The join fails closed on mismatched source/revision/export/declaration/closure,
altered content-addressed observation bytes and cross-branch JMD fingerprints.
"""
from __future__ import annotations

import argparse
import base64
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import stat

from lean_world_builder_contract import pending_from_manifest
from lean_world_native_v3_projection import extract_candidates
from lean_world_native_p1_codec import candidate_receipt
from lean_world_atomic_spool import publish_immutable

HEX64 = re.compile(r"[0-9a-f]{64}\Z")


class ObservationJoinError(ValueError):
    pass


def _loads_unique(raw: bytes) -> dict:
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ObservationJoinError("duplicate observation key")
            result[key] = value
        return result
    try:
        obj = json.loads(raw, object_pairs_hook=unique)
    except (UnicodeError, ValueError) as exc:
        raise ObservationJoinError("invalid observation JSON") from exc
    if type(obj) is not dict:
        raise ObservationJoinError("non-object observation")
    return obj


def _read_regular(path: Path, *, limit: int = 16_000_000) -> bytes:
    if path.is_symlink() or not path.is_file():
        raise ObservationJoinError("unsafe observation file")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        f = os.fstat(fd)
        if not stat.S_ISREG(f.st_mode) or f.st_size > limit:
            raise ObservationJoinError("oversized or nonregular observation")
        raw = os.read(fd, limit + 1)
        if len(raw) > limit or len(raw) != f.st_size:
            raise ObservationJoinError("changed/oversized observation")
        return raw
    finally:
        os.close(fd)


def _read_immutable(path: Path, spool: Path, suffix: str) -> tuple[dict, str]:
    if path.parent.resolve() != spool.resolve():
        raise ObservationJoinError("observation is outside selected immutable spool")
    raw = _read_regular(path)
    digest = sha256(raw).hexdigest()
    if path.name != digest + suffix:
        raise ObservationJoinError("content-addressed observation filename mismatch")
    obj = _loads_unique(raw)
    encoded = (json.dumps(obj, sort_keys=True, separators=(",", ":")) + "\n").encode()
    if raw != encoded:
        raise ObservationJoinError("noncanonical observation encoding")
    return obj, digest


def _require_false(observation: dict, *keys: str) -> None:
    for key in keys:
        if observation.get(key) is not False:
            raise ObservationJoinError("invalid promotion state: " + key)


def _same(a, b, label: str) -> None:
    if type(a) is not type(b) or a != b:
        raise ObservationJoinError("mismatched " + label)


def _decoded(observation: dict, key: str, digest_key: str) -> bytes:
    encoded = observation.get(key)
    if type(encoded) is not str:
        raise ObservationJoinError("missing "+key)
    try:
        raw = base64.b64decode(encoded, validate=True)
    except (ValueError, base64.binascii.Error) as exc:
        raise ObservationJoinError("invalid base64 "+key) from exc
    expected_digest = observation.get(digest_key)
    # Original v3 axiom declarations have no proof expression; the P1
    # exporter receipt records JSON null, not SHA256(empty bytes).
    if not (raw == b"" and expected_digest is None) and \
            sha256(raw).hexdigest() != expected_digest:
        raise ObservationJoinError("wrong digest "+digest_key)
    return raw


def join(manifest: Path, projection_path: Path, checker_path: Path,
         spool: Path, *, jmd_path: Path | None = None,
         jmd_sha256: str | None = None,
         jmd_source_sha256: str | None = None) -> dict:
    """Emit an immutable candidate observation, never an admission receipt."""
    pending = pending_from_manifest(manifest)
    if manifest.parent.resolve() != spool.resolve():
        raise ObservationJoinError("handoff and observations must share spool")
    projection, projection_sha = _read_immutable(
        projection_path, spool, ".native-type-observation.json")
    checker, checker_sha = _read_immutable(
        checker_path, spool, ".checker-observation.json")
    if (projection.get("schema") != "dashi-lean-v3-type-projection-observation-v1"
        or projection.get("status") != "native-v3-type-projected-uncertified"):
        raise ObservationJoinError("unsupported native projection")
    _require_false(projection, "kernel_certified", "world_admitted",
                   "native_dag_complete", "imported_dependencies_resolved")
    for key, expected in (
        ("handoff_key", pending.handoff_key),
        ("artifact_sha256", pending.artifact_sha256),
        ("repository", pending.repository),
        ("revision", pending.revision),
        ("module", pending.module),
        ("declaration", pending.declaration),
        ("toolchain", pending.toolchain),
        ("dependency_closure_id", pending.dependency_closure_id),
        ("source_closure", [list(x) for x in pending.source_closure]),
    ):
        _same(projection.get(key), expected, "projection "+key)
    if projection.get("exported_expr_roundtrip") is not True:
        raise ObservationJoinError("no exact exported expression roundtrip")
    if projection.get("original_source_text_reconstructed_by_codec") is not False:
        raise ObservationJoinError("source text reconstruction falsely promoted")
    selected = extract_candidates(
        pending.artifact, selected_names=frozenset((pending.declaration,)))
    if len(selected) != 1 or selected[0].name != pending.declaration:
        raise ObservationJoinError("no unique original declaration")
    candidate = selected[0]
    module_path = pending.module.replace(".", "/") + ".lean"
    original_source = [x for x in pending.source_closure if x[0] == module_path]
    if len(original_source) != 1:
        if len(pending.source_closure) != 1:
            raise ObservationJoinError("ambiguous original source path")
        original_source = list(pending.source_closure)
    p1 = candidate_receipt(
        candidate, toolchain=pending.toolchain,
        source_sha256=original_source[0][1],
        export_sha256=pending.artifact_sha256)
    for key, expected in (
        ("declaration_kind", candidate.kind),
        ("direct_statement_constants", list(candidate.direct_constants)),
        ("proof_value_present", candidate.proof_value_present),
        ("direct_proof_constants", list(candidate.proof_direct_constants)),
        ("original_source_path", original_source[0][0]),
        ("original_source_sha256", original_source[0][1]),
        ("canonical_type_sha256", candidate.type_sha256),
        ("exact_exported_type_sha256", p1["exact_exported_type_sha256"]),
        ("alpha_type_sha256", p1["alpha_type_sha256"]),
        ("exact_exported_proof_sha256", p1["exact_exported_proof_sha256"]),
    ):
        _same(projection.get(key), expected, "projected original "+key)
    for key, digest_key, expected in (
        ("canonical_type_b64", "canonical_type_sha256", candidate.canonical_type),
        ("exact_exported_type_b64", "exact_exported_type_sha256", p1["exact_type_bytes"]),
        ("alpha_type_b64", "alpha_type_sha256", p1["alpha_type_bytes"]),
        ("exact_exported_proof_b64", "exact_exported_proof_sha256", p1["exact_proof_bytes"]),
    ):
        if _decoded(projection, key, digest_key) != expected:
            raise ObservationJoinError("projected native source bytes changed: "+key)
    if (checker.get("schema") != "dashi-lean-external-check-observation-v1"
        or checker.get("status") != "rust-nanoda-exit-zero-uncertified"
        or checker.get("checker_kind") != "rust-nanoda"):
        raise ObservationJoinError("not an original Rust checker observation")
    _require_false(checker, "kernel_certified", "world_admitted")
    for key, expected in (
        ("handoff_key", pending.handoff_key),
        ("native_manifest_key", pending.handoff_key),
        ("artifact_sha256", pending.artifact_sha256),
    ):
        _same(checker.get(key), expected, "checker "+key)
    for key in ("executable_sha256", "stdout_sha256", "stderr_sha256"):
        if type(checker.get(key)) is not str or not HEX64.fullmatch(checker[key]):
            raise ObservationJoinError("missing original checker digest: "+key)
    argv = checker.get("argv")
    if (type(argv) is not list or len(argv) != 2 or argv[0] != "nanoda-config"
        or type(argv[1]) is not str or not HEX64.fullmatch(argv[1])):
        raise ObservationJoinError("unrecognized Rust checker invocation")

    jmd_digest = None
    if (jmd_path is None) != (jmd_sha256 is None) or (
        jmd_path is None and jmd_source_sha256 is not None):
        raise ObservationJoinError("incomplete JMD identity")
    if jmd_path is not None:
        if not all(type(x) is str and HEX64.fullmatch(x)
                   for x in (jmd_sha256, jmd_source_sha256)):
            raise ObservationJoinError("un-pinned JMD source/observation")
        jmd_raw = _read_regular(jmd_path)
        jmd_digest = sha256(jmd_raw).hexdigest()
        _same(jmd_digest, jmd_sha256, "JMD observation digest")
        jmd = _loads_unique(jmd_raw)
        for key, expected in (
            ("status", "jmd-native-builder-readonly-roots-validated"),
            ("builder_source_sha256", jmd_source_sha256),
            ("native_export_sha256", pending.artifact_sha256),
            ("selected_declaration", pending.declaration),
            ("declaration_kind", candidate.kind),
            ("direct_type_constants", list(candidate.direct_constants)),
            ("direct_proof_constants", list(candidate.proof_direct_constants)),
            ("used_original_jmd_builder_parser", True),
            ("wrote_another_world_database", False),
            ("typechecked_by_lean_here", False),
            ("world_admitted", False),
        ):
            _same(jmd.get(key), expected, "JMD "+key)
        try:
            lean_hash = _loads_unique(pending.artifact.splitlines()[0])[
                "meta"]["lean"]["githash"]
        except (KeyError, TypeError, IndexError) as exc:
            raise ObservationJoinError("native Lean revision missing") from exc
        _same(jmd.get("original_lean_revision"), lean_hash,
              "original Lean revision")

    receipt = {
        "schema": "dashi-lean-cross-pr-observation-join-v1",
        "status": "same-native-export-correlated-uncertified",
        "handoff_key": pending.handoff_key,
        "native_export_sha256": pending.artifact_sha256,
        "repository": pending.repository,
        "revision": pending.revision,
        "module": pending.module,
        "declaration": pending.declaration,
        "toolchain": pending.toolchain,
        "dependency_closure_id": pending.dependency_closure_id,
        "source_closure": [list(x) for x in pending.source_closure],
        "projection_observation_sha256": projection_sha,
        "checker_observation_sha256": checker_sha,
        "rust_checker_executable_sha256": checker["executable_sha256"],
        "jmd_observation_sha256": jmd_digest,
        "original_source_path": original_source[0][0],
        "original_source_sha256": original_source[0][1],
        "exact_type_sha256": candidate.type_sha256,
        "alpha_candidate_sha256": p1["alpha_type_sha256"],
        "proof_value_present": candidate.proof_value_present,
        "native_dag_complete": False,
        "imported_dependencies_resolved": False,
        "checker_semantics_authenticated": False,
        "builder_authority_authenticated": False,
        "world_admitted": False,
        "kernel_certified": False,
        "candidate_admission_authorized": False,
    }
    payload = (json.dumps(receipt, sort_keys=True, separators=(",", ":")) + "\n").encode()
    digest = sha256(payload).hexdigest()
    destination = spool / (digest + ".cross-pr-observation.json")
    publish_immutable(destination, payload)
    return {
        "status": receipt["status"],
        "observation_sha256": digest,
        "path": str(destination),
        "kernel_certified": False,
        "world_admitted": False,
        "candidate_admission_authorized": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--projection", required=True, type=Path)
    parser.add_argument("--checker-observation", required=True, type=Path)
    parser.add_argument("--spool", required=True, type=Path)
    parser.add_argument("--jmd-observation", type=Path)
    parser.add_argument("--jmd-sha256")
    parser.add_argument("--jmd-source-sha256")
    args = parser.parse_args()
    try:
        result = join(
            args.manifest, args.projection, args.checker_observation, args.spool,
            jmd_path=args.jmd_observation, jmd_sha256=args.jmd_sha256,
            jmd_source_sha256=args.jmd_source_sha256)
    except (ValueError, OSError, TypeError, KeyError, IndexError) as exc:
        parser.exit(2, "CROSS_PR_OBSERVATION_INCOMPLETE: " + str(exc) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
