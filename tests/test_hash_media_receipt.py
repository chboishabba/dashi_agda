"""No network: receipt helper hashes locally supplied bytes and excludes media."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/hash_media_receipt.py"
MANIFEST = ROOT / "docs/research/bannon-epstein-video-manifest-20261024.json"


def test_manifest_has_no_fake_media_sha_or_verbatim_transcript():
    x = json.loads(MANIFEST.read_text(encoding="utf-8"))
    assert x["controls"]["do_not_vendor_video"]
    assert x["canonical_original_reel"]["sha256"] is None
    assert x["canonical_original_reel"]["doj_video_object_id"] == "EFTA01600824"
    assert x["canonical_original_reel"]["filename"] == "EFTA01600824.mov"
    assert x["canonical_original_reel"]["source_url"].endswith("/DataSet%2010/EFTA01600824.mov")
    assert x["transcript"]["sha256"] is None
    assert x["transcript"]["kind"] == "third_party_machine_generated_timecoded_transcript"
    assert x["transcript"]["source_video_rendition_id"] == "EFTA01600824"
    assert x["transcript"]["reported_segment_count"] == 1753
    assert x["transcript"]["verified_against_reel"] is False
    assert x["chapter_index"]["kind"] == "third_party_description_not_transcript"
    assert len(x["candidate_public_renditions"]) >= 2
    for item in x["candidate_public_renditions"]:
        assert item["sha256"] is None
        assert item["hash_status"] == "not_computed"


def test_hashes_synthetic_media_and_caption_without_copying(tmp_path):
    media = tmp_path / "synthetic.mp4"
    transcript = tmp_path / "captions.vtt"
    media.write_bytes(b"SYNTHETIC ONLY: not an Epstein interview\x00" * 7)
    transcript.write_bytes(b"WEBVTT\n\n00:00:01.000 --> 00:00:02.000\nExample.\n")
    out = tmp_path / "receipt.json"
    cmd = [
        sys.executable, str(SCRIPT), "--file", str(media),
        "--label", "synthetic-test", "--source-url", "https://example.org/synthetic.mp4",
        "--transcript-file", str(transcript), "--transcript-kind", "supplied-vtt",
        "--out", str(out),
    ]
    done = subprocess.run(cmd, text=True, capture_output=True)
    assert done.returncode == 0, done.stderr
    receipt = json.loads(out.read_text(encoding="utf-8"))
    assert receipt["sha256"] == hashlib.sha256(media.read_bytes()).hexdigest()
    assert receipt["transcript"]["sha256"] == hashlib.sha256(transcript.read_bytes()).hexdigest()
    assert receipt["byte_count"] == media.stat().st_size
    assert receipt["identity_with_doj_master_verified"] is False
    assert receipt["media_bytes_embedded"] is False
    assert receipt["transcript_text_embedded"] is False
    assert "Example." not in out.read_text(encoding="utf-8")


def test_watch_page_cannot_be_falsely_hashed_as_video():
    proc = subprocess.run(
        [
            sys.executable, str(SCRIPT), "--stream-url",
            "http://example.org/watch?v=test", "--label", "bad",
        ],
        text=True, capture_output=True,
    )
    assert proc.returncode != 0
    assert "HTTPS" in proc.stderr


def test_transcript_format_is_explicit(tmp_path):
    path = tmp_path / "example.mp4"
    path.write_bytes(b"synthetic")
    proc = subprocess.run(
        [
            sys.executable, str(SCRIPT), "--file", str(path),
            "--label", "synthetic", "--transcript-file", str(path),
        ],
        text=True, capture_output=True,
    )
    assert proc.returncode != 0
    assert "--transcript-kind" in proc.stderr
