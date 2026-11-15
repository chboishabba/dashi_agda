#!/usr/bin/env python3
"""Offline negative controls for zero-checkout GitHub Lean source inventory."""
import base64
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from lean_remote_source_inventory import (inventory, source_blob, repository_tree, RemoteError)


DATA = b"theorem triv : True := trivial\n"
SHA = hashlib.sha1(b"blob " + str(len(DATA)).encode() + bytes([0]) + DATA).hexdigest()
REV = "a" * 40
REPO = "example/project"


def opener(request):
    url = request.full_url
    if "/git/trees/" in url:
        obj = {"truncated": False, "tree": [
            {"type": "blob", "mode": "100644", "path": "Proof.lean",
             "sha": SHA, "size": len(DATA)},
            {"type": "blob", "mode": "120000", "path": "Alias.lean",
             "sha": SHA, "size": len(DATA)},
            {"type": "blob", "mode": "100644", "path": "README.md",
             "sha": SHA, "size": len(DATA)},
        ]}
    elif "/git/blobs/" in url:
        obj = {"encoding": "base64", "content": base64.b64encode(DATA).decode(),
               "size": len(DATA)}
    else:
        raise AssertionError("unexpected API path")
    return json.dumps(obj).encode()


class Tests(unittest.TestCase):
    def test_inventory_never_materializes_repo(self):
        rows = list(inventory(REPO, REV, opener=opener))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["path"], "Proof.lean")
        self.assertEqual(rows[0]["status"], "source-verified-not-elaborated")
        self.assertEqual(rows[0]["sha256"], hashlib.sha256(DATA).hexdigest())

    def test_verified_blob_callback_receives_exact_source(self):
        received=[]
        rows=list(inventory(
            REPO, REV, opener=opener,
            on_source=lambda receipt, raw: received.append((receipt, raw))))
        self.assertEqual(len(received),1)
        self.assertEqual(received[0][1],DATA)
        self.assertEqual(received[0][0],rows[0])
        self.assertEqual(received[0][0]["git_blob"],SHA)

    def test_skipped_blob_never_calls_source_consumer(self):
        received=[]
        rows=list(inventory(
            REPO,REV,opener=opener,max_blob_bytes=1,
            on_source=lambda receipt,raw:received.append(raw)))
        self.assertEqual(received,[])
        self.assertEqual(rows[0]["status"],"skipped-size-cap")

    def test_skips_oversized_without_loading_blob(self):
        def tree_only(req):
            if "/git/blobs/" in req.full_url:
                raise AssertionError("blob should not be downloaded")
            return opener(req)
        rows = list(inventory(REPO, REV, opener=tree_only, max_blob_bytes=1))
        self.assertEqual(rows[0]["status"], "skipped-size-cap")

    def test_rejects_truncated_tree(self):
        def truncated(req):
            return json.dumps({"truncated": True, "tree": []}).encode()
        with self.assertRaises(RemoteError):
            repository_tree(REPO, REV, opener=truncated)

    def test_rejects_unpinned_revision(self):
        with self.assertRaises(ValueError):
            repository_tree(REPO, "master", opener=opener)

    def test_rejects_wrong_blob_identity(self):
        with self.assertRaises(RemoteError):
            source_blob(REPO, "0" * 40, 1024, opener=opener)

    def test_rejects_wrong_blob_size(self):
        def wrong_size(req):
            return json.dumps({"encoding":"base64",
                               "content":base64.b64encode(DATA).decode(),
                               "size":len(DATA)+1}).encode()
        with self.assertRaises(RemoteError):
            source_blob(REPO, SHA, 1024, opener=wrong_size)


if __name__ == "__main__":
    unittest.main()
