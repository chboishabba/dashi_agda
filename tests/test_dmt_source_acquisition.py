"""Synthetic source-acquisition contract, not actual participant data or rights approval."""
import hashlib
import importlib.util
import json
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "dmt_source_acquisition", ROOT/"scripts/acquire_dmt_imaging_source.py")
src = importlib.util.module_from_spec(spec)
spec.loader.exec_module(src)


def test_missing_rights_review_blocks_before_network_access(tmp_path):
    with pytest.raises(ValueError, match="rights/consent"):
        src.acquire(tmp_path/"out", tmp_path/"nonexistent-approval",
                    tmp_path/"nonexistent-receipt")
    assert not (tmp_path/"out").exists()


def test_local_source_blob_verification_and_corruption_rejection(tmp_path):
    payload = b"NOT CLINICAL DATA: synthetic test"
    local = tmp_path/"data"
    (local/"fMRI").mkdir(parents=True)
    (local/"fMRI"/"LongS01DMT.mat").write_bytes(payload)
    digest = hashlib.sha1(
        b"blob " + str(len(payload)).encode("ascii") + b"\0" + payload
    ).hexdigest()
    receipt = {
        "source_repository": "timmer500/DMT_Imaging",
        "source_commit": src.SOURCE_COMMIT,
        "inventory": {"file_count": 1},
        "files": [{"path": "fMRI/LongS01DMT.mat",
                   "size_bytes": len(payload), "git_blob_sha1": digest}],
    }
    path = tmp_path/"synthetic-receipt.json"
    path.write_text(json.dumps(receipt), encoding="utf-8")
    result = src.verify_checkout(local, path)
    assert result["status"] == "git_source_checkout_verified"
    assert result["source_files_verified"] == 1
    assert result["human_analysis_reproduced"] is False
    assert result["rights_granted_by_script"] is False
    (local/"fMRI"/"LongS01DMT.mat").write_bytes(payload + b"CORRUPT")
    with pytest.raises(ValueError, match="byte-size mismatch"):
        src.verify_checkout(local, path)
