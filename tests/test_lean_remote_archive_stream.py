#!/usr/bin/env python3
"""Offline regression tests for no-disk public GitHub archive streaming."""
import hashlib
import io
from pathlib import Path
import sys
import tarfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_remote_archive_stream import stream_archive, ArchiveError

REPO = "owner/repo"
REV = "a" * 40
DATA = b"theorem foo : True := trivial\n"


def archive_fixture(members):
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w:gz") as archive:
        for name, content in members:
            info = tarfile.TarInfo(name)
            info.size = len(content)
            archive.addfile(info, io.BytesIO(content))
    raw.seek(0)
    return raw


class Tests(unittest.TestCase):
    def test_streams_git_identity_without_checkout(self):
        src = archive_fixture([
            ("repo-aaaa/README.md", b"ignored"),
            ("repo-aaaa/src/Foo.lean", DATA),
        ])
        rows = list(stream_archive(src, REPO, REV))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["path"], "src/Foo.lean")
        self.assertEqual(rows[0]["sha256"], hashlib.sha256(DATA).hexdigest())
        git_sha = hashlib.sha1(b"blob " + str(len(DATA)).encode() +
                               bytes([0]) + DATA).hexdigest()
        self.assertEqual(rows[0]["git_blob"], git_sha)
        self.assertEqual(rows[0]["status"], "source-verified-not-elaborated")

    def test_reports_skipped_files(self):
        src = archive_fixture([("repo-aaaa/Foo.lean", DATA)])
        rows = list(stream_archive(src, REPO, REV, max_file_bytes=3))
        self.assertEqual(rows[0]["status"], "skipped-size-cap")

    def test_rejects_overall_limit(self):
        src = archive_fixture([("repo-aaaa/Foo.lean", DATA)])
        with self.assertRaises(ArchiveError):
            list(stream_archive(src, REPO, REV, max_total_bytes=3))

    def test_transfer_budget_includes_nonlean_files(self):
        src = archive_fixture([("repo-aaaa/README.md", b"x" * 20000),
                               ("repo-aaaa/Foo.lean", DATA)])
        with self.assertRaises(ArchiveError):
            list(stream_archive(src, REPO, REV, max_transfer_bytes=32))

    def test_empty_archive(self):
        src = archive_fixture([("repo-aaaa/README.md", b"x")])
        self.assertEqual(list(stream_archive(src, REPO, REV)), [])

    def test_rejects_unpinned_revision(self):
        src = archive_fixture([("repo-aaaa/Foo.lean", DATA)])
        with self.assertRaises(ValueError):
            list(stream_archive(src, REPO, "master"))

    def test_multiple_source_files(self):
        src = archive_fixture([
            ("repo-aaaa/A.lean", DATA),
            ("repo-aaaa/B.lean", DATA),
        ])
        self.assertEqual(len(list(stream_archive(src, REPO, REV))), 2)


if __name__ == "__main__":
    unittest.main()
