#!/usr/bin/env python3
"""Offline exact-byte source world tests: both existing no-checkout paths."""
from __future__ import annotations
import base64
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_world_source_world import SourceWorldBuilder, SourceConflict

DATA = b"theorem foo : True := trivial\n"
GIT = hashlib.sha1(b"blob " + str(len(DATA)).encode() + b"\0" + DATA).hexdigest()
SHA = hashlib.sha256(DATA).hexdigest()
REPO, REV = "owner/repo", "a"*40


def archive_fixture(members):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w:gz") as tar:
        for path, data in members:
            item = tarfile.TarInfo(path)
            item.size = len(data)
            tar.addfile(item, io.BytesIO(data))
    stream.seek(0)
    return stream


def rest_opener(request):
    if "/git/trees/" in request.full_url:
        return json.dumps({"truncated": False, "tree": [{
            "mode": "100644", "type": "blob", "path": "Foo.lean",
            "sha": GIT, "size": len(DATA),
        }]}).encode()
    if "/git/blobs/" in request.full_url:
        return json.dumps({"encoding": "base64",
                           "content": base64.b64encode(DATA).decode(),
                           "size": len(DATA)}).encode()
    raise AssertionError("unexpected network call")


class Tests(unittest.TestCase):
    def test_archive_feeds_exact_verified_source_into_world(self):
        received = []
        builder = SourceWorldBuilder(lambda receipt, raw: received.append((receipt, raw)))
        count = builder.ingest_archive(
            archive_fixture([("repo-root/README", b"not Lean"),
                             ("repo-root/Foo.lean", DATA)]), REPO, REV)
        self.assertEqual(count, 1)
        self.assertEqual(received[0][1], DATA)
        self.assertEqual(received[0][0]["git_blob"], GIT)
        manifest = list(builder.manifest())
        self.assertEqual(len(manifest), 1)
        self.assertEqual(manifest[0]["status"], "source-verified-not-elaborated")
        self.assertNotIn("canonical_type", manifest[0])
        self.assertNotIn("source_bytes", builder.manifest_jsonl())
        self.assertEqual(builder.counters()["elaborated_declarations"], 0)

    def test_rest_feeds_same_original_bytes_without_checkout(self):
        received = []
        builder = SourceWorldBuilder(lambda r, b: received.append(b))
        self.assertEqual(builder.ingest_rest(
            REPO, REV, opener=rest_opener), 1)
        self.assertEqual(received, [DATA])
        self.assertEqual(list(builder.manifest())[0]["sha256"], SHA)

    def test_archive_and_rest_are_idempotent_same_source(self):
        builder = SourceWorldBuilder()
        builder.ingest_archive(archive_fixture([
            ("root/Foo.lean", DATA)]), REPO, REV)
        builder.ingest_rest(REPO, REV, opener=rest_opener)
        self.assertEqual(builder.counters()["source_occurrences"], 1)

    def test_distinct_source_occurrences_not_lost_by_blob_interning(self):
        builder = SourceWorldBuilder()
        builder.ingest_archive(archive_fixture([
            ("root/A.lean", DATA), ("root/B.lean", DATA)]), REPO, REV)
        self.assertEqual(builder.counters()["source_occurrences"], 2)
        self.assertEqual(builder.counters()["source_hash_candidate_groups"], 1)

    def test_digest_mismatch_is_rejected_before_consumer(self):
        seen = []
        builder = SourceWorldBuilder(lambda r, b: seen.append(b))
        receipt = {"repository": REPO, "revision": REV, "path": "Foo.lean",
                   "git_blob": GIT, "sha256": "0"*64, "size": len(DATA),
                   "status": "source-verified-not-elaborated"}
        with self.assertRaises(SourceConflict):
            builder.admit(receipt, DATA)
        self.assertEqual(seen, [])

    def test_conflicting_pinned_origin_is_rejected(self):
        builder = SourceWorldBuilder()
        one = {"repository": REPO, "revision": REV, "path": "Foo.lean",
               "git_blob": GIT, "sha256": SHA, "size": len(DATA),
               "status": "source-verified-not-elaborated"}
        self.assertTrue(builder.admit(one, DATA))
        altered = dict(one, status="skipped-size-cap")
        with self.assertRaises(SourceConflict):
            builder.admit(altered, DATA)

    def test_cap_exclusions_are_not_promoted(self):
        builder = SourceWorldBuilder()
        builder.ingest_archive(
            archive_fixture([("root/Foo.lean", DATA)]), REPO, REV,
            max_file_bytes=1)
        self.assertEqual(builder.counters()["source_occurrences"], 0)
        self.assertEqual(builder.counters()["skipped_size_cap"], 1)

    def test_downstream_rejection_leaves_no_source_receipt(self):
        def fail(receipt, raw):
            raise RuntimeError("Lean elaborator rejected")
        builder = SourceWorldBuilder(fail)
        with self.assertRaises(RuntimeError):
            builder.ingest_archive(
                archive_fixture([("root/Foo.lean", DATA)]), REPO, REV)
        self.assertEqual(list(builder.manifest()), [])

    def test_source_callback_never_fires_for_skipped_file(self):
        seen = []
        builder = SourceWorldBuilder(lambda r, b: seen.append(b))
        builder.ingest_archive(archive_fixture([
            ("root/Foo.lean", DATA)]), REPO, REV, max_file_bytes=1)
        self.assertEqual(seen, [])

    def test_archive_transfer_budget_fail_closed(self):
        builder = SourceWorldBuilder()
        with self.assertRaises(Exception):
            builder.ingest_archive(archive_fixture([
                ("root/README", b"z"*20000), ("root/Foo.lean", DATA)]),
                REPO, REV, max_transfer_bytes=32)


if __name__ == "__main__":
    unittest.main()
