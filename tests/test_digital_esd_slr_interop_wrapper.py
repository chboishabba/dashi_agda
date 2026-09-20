from __future__ import annotations

import importlib.util
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "interop_scripts" / "digital_esd_slr.py"

spec = importlib.util.spec_from_file_location("digital_esd_slr", MODULE_PATH)
assert spec and spec.loader
interop = importlib.util.module_from_spec(spec)
spec.loader.exec_module(interop)


def write_jsonl(path: Path, rows: list[dict]) -> None:
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row) + "\n")


def test_prepare_and_verify_same_object_receipts(tmp_path: Path) -> None:
    digest = "a" * 64
    source = tmp_path / "canonical.jsonl"
    request = tmp_path / "requests.jsonl"
    manifest = tmp_path / "request-manifest.json"

    write_jsonl(
        source,
        [{
            "source_identity_reference": "ERIC:EJ1",
            "source_revision_ref": f"fulltext-sha256:{digest}",
            "content_digest_ref": f"sha256:{digest}",
            "artifact_path": "/tmp/paper.pdf",
            "candidate_only": True,
            "creates_semantic_authority": False,
            "applicability_promoted": False,
            "claim_truth_promoted": False,
            "creates_source_audit_admission": False,
        }],
    )

    args = type("Args", (), {
        "input": source,
        "output": request,
        "manifest": manifest,
    })()
    assert interop.cmd_prepare(args) == 0

    receipts = tmp_path / "receipts.jsonl"
    write_jsonl(
        receipts,
        [{
            "source_identity_reference": "ERIC:EJ1",
            "source_revision_ref": f"fulltext-sha256:{digest}",
            "content_digest_ref": f"sha256:{digest}",
            "observation_ref": "observation:test",
            "candidate_only": True,
            "creates_semantic_authority": False,
            "applicability_promoted": False,
            "claim_truth_promoted": False,
        }],
    )

    verified = tmp_path / "verified.json"
    verify_args = type("Args", (), {
        "input": request,
        "receipts": receipts,
        "output": verified,
    })()
    assert interop.cmd_verify(verify_args) == 0

    receipt = json.loads(verified.read_text(encoding="utf-8"))
    assert receipt["source_identity_reconciled"] is True
    assert receipt["source_revision_reconciled"] is True
    assert receipt["content_digest_reconciled"] is True
    assert receipt["candidate_only_verified"] is True
    assert receipt["creates_source_audit_admission"] is False


def test_verify_rejects_digest_drift(tmp_path: Path) -> None:
    request = tmp_path / "requests.jsonl"
    receipts = tmp_path / "receipts.jsonl"
    write_jsonl(
        request,
        [{
            "source_identity_reference": "ERIC:EJ1",
            "source_revision_ref": "rev:1",
            "content_digest_ref": "sha256:" + "a" * 64,
        }],
    )
    write_jsonl(
        receipts,
        [{
            "source_identity_reference": "ERIC:EJ1",
            "source_revision_ref": "rev:1",
            "content_digest_ref": "sha256:" + "b" * 64,
            "observation_ref": "observation:test",
            "candidate_only": True,
            "creates_semantic_authority": False,
            "applicability_promoted": False,
            "claim_truth_promoted": False,
        }],
    )

    args = type("Args", (), {
        "input": request,
        "receipts": receipts,
        "output": tmp_path / "verified.json",
    })()

    try:
        interop.cmd_verify(args)
    except RuntimeError as exc:
        assert "digest mismatch" in str(exc)
    else:
        raise AssertionError("digest drift should fail closed")
