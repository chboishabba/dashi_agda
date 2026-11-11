#!/usr/bin/env python3
"""World-builder source-acquisition boundary: pinned, no checkout, no false Lean claims.

This is the upstream source world, not the elaborated declaration/proof world.
It consumes BOTH existing acquisition interfaces via verified-source callbacks.
The typed downstream interface receives (receipt, exact source bytes) only when
the source has passed the hash and byte-size checks. A manifest can be emitted
without persisting the original source or allocating a repository checkout.

No Lean semantic projection, type identity or kernel validity is inferred.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Callable, Iterable, BinaryIO

import lean_remote_archive_stream as archive
import lean_remote_source_inventory as rest


class SourceConflict(ValueError):
    pass


@dataclass(frozen=True)
class SourceOrigin:
    repository: str
    revision: str
    path: str


class SourceWorldBuilder:
    """One pinned source-world occurrence per path; exact verified blob receipts.

    Stores only source receipts, never caches all source bytes. A consumer may
    pass each verified source to an isolated Lean worker synchronously.  A
    matching digest is only a content-addressing candidate until exact bytes
    are compared by a persistent store; no Lean type-level dedup occurs here.
    """
    def __init__(self, consumer: Callable[[dict, bytes], None] | None = None):
        self._by_origin: dict[SourceOrigin, dict] = {}
        self._hash_candidates: dict[tuple[str, int], set[SourceOrigin]] = {}
        self._consumer = consumer
        self.skipped = 0

    @staticmethod
    def _validate_receipt(receipt: dict, raw: bytes):
        expected = ("repository", "revision", "path", "git_blob",
                    "sha256", "size", "status")
        if any(k not in receipt for k in expected):
            raise SourceConflict("missing original source provenance")
        if receipt["status"] != "source-verified-not-elaborated":
            raise SourceConflict("unverified source cannot enter the world")
        if type(raw) is not bytes or type(receipt["size"]) is not int:
            raise SourceConflict("invalid original source bytes or size")
        if len(raw) != receipt["size"]:
            raise SourceConflict("source length mismatch")
        actual_sha = hashlib.sha256(raw).hexdigest()
        git_blob = hashlib.sha1(
            b"blob " + str(len(raw)).encode("ascii") + bytes([0]) + raw
        ).hexdigest()
        if actual_sha != receipt["sha256"] or git_blob != receipt["git_blob"]:
            raise SourceConflict("source digest/identity mismatch")
        for field in ("repository", "revision", "path"):
            if not isinstance(receipt[field], str) or not receipt[field]:
                raise SourceConflict("empty or invalid source origin")
        source_path = receipt["path"]
        if (not source_path.endswith(".lean") or source_path.startswith("/")
            or chr(0) in source_path
            or any(part in ("", ".", "..") for part in source_path.split("/"))):
            raise SourceConflict("unsafe original Lean source path")
        import re
        if re.fullmatch(r"[0-9a-fA-F]{40}", receipt["revision"]) is None:
            raise SourceConflict("source provenance requires immutable revision")

    def admit(self, receipt: dict, raw: bytes) -> bool:
        self._validate_receipt(receipt, raw)
        origin = SourceOrigin(
            receipt["repository"], receipt["revision"], receipt["path"])
        old = self._by_origin.get(origin)
        if old is not None:
            if old != receipt:
                raise SourceConflict("conflicting source for same pinned origin")
            return False
        # Fail without a persisted occurrence if downstream elaboration rejects.
        if self._consumer is not None:
            self._consumer(dict(receipt), raw)
        self._by_origin[origin] = dict(receipt)
        key = (receipt["sha256"], receipt["size"])
        self._hash_candidates.setdefault(key, set()).add(origin)
        return True

    def skip(self, receipt: dict):
        if receipt.get("status") != "skipped-size-cap":
            raise SourceConflict("only explicit capped source exclusions admitted")
        self.skipped += 1

    def ingest_archive(self, source: BinaryIO, repository: str, revision: str,
                       **limits) -> int:
        count = 0
        for receipt in archive.stream_archive(
                source, repository, revision, on_source=self.admit, **limits):
            if receipt["status"] == "skipped-size-cap":
                self.skip(receipt)
            else:
                count += 1
        return count

    def ingest_rest(self, repository: str, revision: str,
                    **kwargs) -> int:
        count = 0
        for receipt in rest.inventory(
                repository, revision, on_source=self.admit, **kwargs):
            if receipt["status"] == "skipped-size-cap":
                self.skip(receipt)
            else:
                count += 1
        return count

    def manifest(self):
        # SourceOrigin is intentionally a value object, not an ordering type.
        # Use its stable provenance tuple for deterministic manifests instead
        # of relying on dataclass ordering being enabled.
        for key in sorted(self._by_origin,
                          key=lambda origin: (origin.repository,
                                              origin.revision,
                                              origin.path)):
            record = dict(self._by_origin[key])
            record["kind"] = "world-source-occurrence"
            # Deliberately no elaboration/statement identity.
            yield record

    def counters(self) -> dict:
        return {"source_occurrences": len(self._by_origin),
                "source_hash_candidate_groups": len(self._hash_candidates),
                "skipped_size_cap": self.skipped,
                "elaborated_declarations": 0, "kernel_checked_declarations": 0}

    def manifest_jsonl(self) -> str:
        return "".join(json.dumps(x, sort_keys=True) + "\n"
                       for x in self.manifest())
