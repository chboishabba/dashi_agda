#!/usr/bin/env python3
"""Deterministic offline field-capture and verification.

This module never performs network I/O. It copies source bytes into an isolated
payload directory and records a canonical SHA-256 manifest that can be verified
later without access to the original source.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Iterable


FORMAT = "dashi-offline-capture/v1"
MANIFEST_NAME = "manifest.json"
PAYLOAD_DIR = "payload"


class CaptureError(RuntimeError):
    """Raised when a capture or verification invariant fails."""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _entry_digest(entries: list[dict[str, object]]) -> str:
    canonical = json.dumps(
        entries,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def _is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def _source_files(source: Path) -> Iterable[tuple[Path, str]]:
    if source.is_symlink():
        raise CaptureError(f"symlink source is not allowed: {source}")

    if source.is_file():
        yield source, source.name
        return

    if not source.is_dir():
        raise CaptureError(f"source is not a regular file or directory: {source}")

    for root, dirnames, filenames in os.walk(source, followlinks=False):
        root_path = Path(root)
        dirnames.sort()
        filenames.sort()

        for dirname in list(dirnames):
            candidate = root_path / dirname
            if candidate.is_symlink():
                raise CaptureError(f"symlink directory is not allowed: {candidate}")

        for filename in filenames:
            candidate = root_path / filename
            if candidate.is_symlink():
                raise CaptureError(f"symlink file is not allowed: {candidate}")
            if not candidate.is_file():
                raise CaptureError(f"non-regular source entry is not allowed: {candidate}")
            relative = candidate.relative_to(source).as_posix()
            yield candidate, relative


def _manifest(label: str, entries: list[dict[str, object]]) -> dict[str, object]:
    return {
        "format": FORMAT,
        "label": label,
        "files": entries,
        "content_sha256": _entry_digest(entries),
    }


def _canonical_json_bytes(value: dict[str, object]) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            indent=2,
            ensure_ascii=False,
        )
        + "\n"
    ).encode("utf-8")


def capture(source: Path, destination: Path, label: str) -> dict[str, object]:
    source = source.expanduser()
    destination = destination.expanduser()

    if not label or label.strip() != label:
        raise CaptureError("label must be non-empty and must not have outer whitespace")

    if source.is_symlink():
        raise CaptureError(f"symlink source is not allowed: {source}")

    source_resolved = source.resolve(strict=True)
    destination_resolved = destination.resolve(strict=False)

    source_container = source_resolved if source_resolved.is_dir() else source_resolved.parent
    if _is_relative_to(destination_resolved, source_container):
        raise CaptureError("destination must be outside the captured source tree")

    if destination.exists():
        raise CaptureError(f"destination already exists: {destination}")

    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(
        tempfile.mkdtemp(
            prefix=f".{destination.name}.capture-",
            dir=str(destination.parent),
        )
    )

    try:
        payload = temporary / PAYLOAD_DIR
        payload.mkdir()

        entries: list[dict[str, object]] = []
        for original, relative in _source_files(source_resolved):
            target = payload / Path(relative)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, target)
            entries.append(
                {
                    "path": relative,
                    "sha256": _sha256_file(target),
                    "size": target.stat().st_size,
                }
            )

        entries.sort(key=lambda entry: str(entry["path"]))
        manifest = _manifest(label, entries)
        (temporary / MANIFEST_NAME).write_bytes(_canonical_json_bytes(manifest))
        temporary.replace(destination)
        return manifest
    except Exception:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def _load_manifest(capture_dir: Path) -> dict[str, object]:
    manifest_path = capture_dir / MANIFEST_NAME
    if not manifest_path.is_file() or manifest_path.is_symlink():
        raise CaptureError(f"missing regular manifest: {manifest_path}")
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CaptureError(f"invalid manifest: {exc}") from exc

    required = {"format", "label", "files", "content_sha256"}
    if set(manifest) != required:
        raise CaptureError("manifest keys do not match the v1 contract")
    if manifest["format"] != FORMAT:
        raise CaptureError(f"unsupported manifest format: {manifest['format']!r}")
    if not isinstance(manifest["label"], str) or not manifest["label"]:
        raise CaptureError("manifest label must be a non-empty string")
    if not isinstance(manifest["files"], list):
        raise CaptureError("manifest files must be a list")
    if not isinstance(manifest["content_sha256"], str):
        raise CaptureError("manifest content_sha256 must be a string")
    return manifest


def verify(capture_dir: Path) -> dict[str, object]:
    capture_dir = capture_dir.expanduser().resolve(strict=True)
    manifest = _load_manifest(capture_dir)
    payload = capture_dir / PAYLOAD_DIR

    if not payload.is_dir() or payload.is_symlink():
        raise CaptureError(f"missing regular payload directory: {payload}")

    expected_entries = manifest["files"]
    assert isinstance(expected_entries, list)

    normalized_expected: list[dict[str, object]] = []
    seen: set[str] = set()

    for raw in expected_entries:
        if not isinstance(raw, dict) or set(raw) != {"path", "sha256", "size"}:
            raise CaptureError("manifest file entry does not match the v1 contract")

        relative = raw["path"]
        digest = raw["sha256"]
        size = raw["size"]

        if not isinstance(relative, str) or not relative:
            raise CaptureError("manifest path must be a non-empty string")
        relative_path = Path(relative)
        if relative_path.is_absolute() or ".." in relative_path.parts:
            raise CaptureError(f"unsafe manifest path: {relative}")
        if relative_path.as_posix() != relative:
            raise CaptureError(f"manifest path must use canonical POSIX separators: {relative}")
        if relative in seen:
            raise CaptureError(f"duplicate manifest path: {relative}")
        seen.add(relative)

        if not isinstance(digest, str) or len(digest) != 64:
            raise CaptureError(f"invalid SHA-256 for {relative}")
        try:
            int(digest, 16)
        except ValueError as exc:
            raise CaptureError(f"invalid SHA-256 for {relative}") from exc

        if not isinstance(size, int) or isinstance(size, bool) or size < 0:
            raise CaptureError(f"invalid size for {relative}")

        target = payload / relative_path
        if target.is_symlink() or not target.is_file():
            raise CaptureError(f"missing regular payload file: {relative}")
        actual_size = target.stat().st_size
        actual_digest = _sha256_file(target)
        if actual_size != size:
            raise CaptureError(
                f"size mismatch for {relative}: expected {size}, got {actual_size}"
            )
        if actual_digest != digest:
            raise CaptureError(f"SHA-256 mismatch for {relative}")

        normalized_expected.append(
            {"path": relative, "sha256": digest, "size": size}
        )

    normalized_expected.sort(key=lambda entry: str(entry["path"]))
    if normalized_expected != expected_entries:
        raise CaptureError("manifest file entries are not in canonical path order")

    actual_paths: list[str] = []
    for root, dirnames, filenames in os.walk(payload, followlinks=False):
        root_path = Path(root)
        dirnames.sort()
        filenames.sort()
        for dirname in dirnames:
            if (root_path / dirname).is_symlink():
                raise CaptureError(f"payload contains symlink directory: {root_path / dirname}")
        for filename in filenames:
            path = root_path / filename
            if path.is_symlink() or not path.is_file():
                raise CaptureError(f"payload contains non-regular file: {path}")
            actual_paths.append(path.relative_to(payload).as_posix())

    if sorted(actual_paths) != sorted(seen):
        unexpected = sorted(set(actual_paths) - seen)
        missing = sorted(seen - set(actual_paths))
        raise CaptureError(
            f"payload path set mismatch; unexpected={unexpected}, missing={missing}"
        )

    expected_content_digest = _entry_digest(normalized_expected)
    if manifest["content_sha256"] != expected_content_digest:
        raise CaptureError("manifest content_sha256 does not match canonical file entries")

    return manifest


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Deterministic offline field capture with SHA-256 verification."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    capture_parser = subparsers.add_parser("capture", help="create a new offline capture")
    capture_parser.add_argument("source", type=Path)
    capture_parser.add_argument("destination", type=Path)
    capture_parser.add_argument("--label", required=True)

    verify_parser = subparsers.add_parser("verify", help="verify an existing capture")
    verify_parser.add_argument("capture_dir", type=Path)

    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "capture":
            manifest = capture(args.source, args.destination, args.label)
        else:
            manifest = verify(args.capture_dir)
    except (CaptureError, OSError) as exc:
        print(f"offline-capture: {exc}", file=sys.stderr)
        return 2

    print(
        json.dumps(
            {
                "format": manifest["format"],
                "label": manifest["label"],
                "files": len(manifest["files"]),
                "content_sha256": manifest["content_sha256"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
