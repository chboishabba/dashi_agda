#!/usr/bin/env python3
"""Pinned #1484 JMD PR105 parser -> immutable READ-ONLY native observation.

The dynamically imported original JMD source MUST have an operator-supplied
SHA256, and the native-v3 export MUST have its own SHA256. We never call the
JMD SQLite world writer or certify Lean typing. The content-addressed JSON
is intended only for #1495's same-export candidate observation join.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import stat
import tempfile

from lean_world_jmd_native_owner_readonly import read_only_check

HEX64 = re.compile(r"[a-f0-9]{64}\Z")

# Exact original dashi_lean4 PR #105 at 62bc54b67651d6dd465585d42490beea8fd2621e.
# Changing this pin requires explicit source/format review, not branch drift.
JMD_PR105_SOURCE_SHA256 = "f937850cbc5ad15a1bc81fa88f723dd1ac3056a2709b7c06ceefe5c22ec5044e"


class JMDObservationError(ValueError):
    pass


def _pinned_file(path: Path, expected: str, *, size_limit: int) -> bytes:
    if type(expected) is not str or not HEX64.fullmatch(expected):
        raise JMDObservationError("missing source/export SHA256 pin")
    if path.is_symlink() or not path.is_file():
        raise JMDObservationError("unsafe pinned input")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0))
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode) or st.st_size > size_limit:
            raise JMDObservationError("invalid pinned input size/type")
        chunks = []
        total = 0
        while True:
            chunk = os.read(fd, min(1024 * 1024, size_limit + 1 - total))
            if not chunk:
                break
            total += len(chunk)
            if total > size_limit:
                raise JMDObservationError("pinned input size exceeded")
            chunks.append(chunk)
        raw = b"".join(chunks)
        if len(raw) != st.st_size or sha256(raw).hexdigest() != expected:
            raise JMDObservationError("pinned JMD source/native export changed")
        return raw
    finally:
        os.close(fd)


def _immutable(spool: Path, payload: bytes) -> Path:
    if spool.is_symlink() or not spool.is_dir():
        raise JMDObservationError("selected private observation spool missing/unsafe")
    destination = spool / (sha256(payload).hexdigest() + ".jmd-readonly-observation.json")
    fd, temporary = tempfile.mkstemp(prefix=".jmd-readonly-", dir=spool)
    try:
        with os.fdopen(fd, "wb") as output:
            output.write(payload)
            output.flush()
            os.fsync(output.fileno())
        try:
            os.link(temporary, destination)
        except FileExistsError:
            if destination.is_symlink() or destination.read_bytes() != payload:
                raise JMDObservationError("conflicting content-addressed JMD observation")
        dir_fd = os.open(spool, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        try:
            os.fsync(dir_fd)
        finally:
            os.close(dir_fd)
    finally:
        os.unlink(temporary)
    return destination


def publish_jmd_readonly(*, source_path: Path, source_sha256: str,
                         export_path: Path, export_sha256: str,
                         declaration: str, spool: Path) -> dict:
    if source_sha256 != JMD_PR105_SOURCE_SHA256:
        raise JMDObservationError("original JMD PR105 source revision not pinned")
    if source_path.name != "build_jmd_lean_ast_world.py":
        raise JMDObservationError("not the pinned original JMD builder path")
    source_bytes = _pinned_file(source_path, source_sha256, size_limit=5_000_000)
    export_bytes = _pinned_file(export_path, export_sha256, size_limit=200_000_000)
    if type(declaration) is not str or not declaration:
        raise JMDObservationError("original selected declaration required")
    try:
        result = read_only_check(
            source_path=source_path, export_path=export_path,
            declaration=declaration, expected_export_sha=export_sha256)
    except (ValueError, KeyError, TypeError, AttributeError, ImportError) as exc:
        raise JMDObservationError("pinned original JMD parser rejected native input") from exc
    if (result.get("status") != "jmd-native-builder-readonly-roots-validated"
        or result.get("builder_source_sha256") != source_sha256
        or result.get("native_export_sha256") != export_sha256
        or result.get("selected_declaration") != declaration
        or result.get("used_original_jmd_builder_parser") is not True
        or result.get("wrote_another_world_database") is not False
        or result.get("typechecked_by_lean_here") is not False
        or result.get("world_admitted") is not False):
        raise JMDObservationError("JMD parser returned invalid source authority")
    # The source is dynamically imported by the existing JMD reader.
    # A before/after pin is necessary, but not full executable/closure
    # authentication or protection against privileged concurrent mutation.
    _pinned_file(source_path, source_sha256, size_limit=5_000_000)
    _pinned_file(export_path, export_sha256, size_limit=200_000_000)
    payload = (json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n").encode()
    destination = _immutable(spool, payload)
    return {
        "status": "jmd-native-builder-readonly-roots-validated",
        "observation_sha256": sha256(payload).hexdigest(),
        "builder_source_sha256": sha256(source_bytes).hexdigest(),
        "native_export_sha256": sha256(export_bytes).hexdigest(),
        "path": str(destination),
        "typechecked_by_lean_here": False,
        "world_admitted": False,
        "kernel_certified": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--builder-source", type=Path, required=True)
    parser.add_argument("--builder-sha256", required=True)
    parser.add_argument("--native-export", type=Path, required=True)
    parser.add_argument("--native-sha256", required=True)
    parser.add_argument("--declaration", required=True)
    parser.add_argument("--spool", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = publish_jmd_readonly(
            source_path=args.builder_source,
            source_sha256=args.builder_sha256,
            export_path=args.native_export,
            export_sha256=args.native_sha256,
            declaration=args.declaration,
            spool=args.spool)
    except (OSError, ValueError, KeyError, TypeError, ImportError) as exc:
        parser.exit(2, "JMD_READONLY_OBSERVATION_INCOMPLETE: " + str(exc) + "\n")
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
