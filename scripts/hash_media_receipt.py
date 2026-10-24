#!/usr/bin/env python3
"""Hash exact media/transcript bytes into a small provenance receipt, never copying media.

Examples:
  python scripts/hash_media_receipt.py --file /safe/local/reel.mp4 --source-url https://example.org/reel.mp4 --label released-reel
  python scripts/hash_media_receipt.py --stream-url https://example.org/direct-reel.mp4 --label source-reel --transcript-file /safe/local/captions.vtt --transcript-kind supplied-vtt

A YouTube watch-page URL is NOT a direct video stream and will be rejected.
SHA-256 of a re-encode does not establish its identity with an original camera reel.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from contextlib import closing
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlsplit
from urllib.request import Request, urlopen

CHUNK = 1024 * 1024
MAX_BYTES = 8 * 1024 * 1024 * 1024


def digest_stream(stream, maximum: int = MAX_BYTES) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    while True:
        piece = stream.read(CHUNK)
        if not piece:
            break
        size += len(piece)
        if size > maximum:
            raise ValueError(f"byte limit exceeded: {maximum}")
        digest.update(piece)
    return digest.hexdigest(), size


def digest_local(path: Path, maximum: int = MAX_BYTES) -> tuple[str, int]:
    if not path.is_file():
        raise ValueError(f"not a regular file: {path}")
    with path.open("rb") as stream:
        return digest_stream(stream, maximum)


def digest_https_media(url: str, maximum: int = MAX_BYTES) -> tuple[str, int, str]:
    if urlsplit(url).scheme != "https":
        raise ValueError("direct media streaming requires HTTPS")
    request = Request(url, headers={"User-Agent": "DASHI media digest receipt/1.0"})
    with closing(urlopen(request, timeout=45)) as stream:
        resolved = stream.geturl()
        if urlsplit(resolved).scheme != "https":
            raise ValueError("redirected to non-HTTPS URL")
        media_type = stream.headers.get_content_type()
        if not (media_type.startswith("video/") or media_type == "application/octet-stream"):
            raise ValueError(f"URL did not return video or octet-stream bytes: {media_type}")
        sha, length = digest_stream(stream, maximum)
    return sha, length, resolved


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sources = p.add_mutually_exclusive_group(required=True)
    sources.add_argument("--file", type=Path, help="existing local rendition; never copied")
    sources.add_argument("--stream-url", help="DIRECT HTTPS video file, streamed but never stored")
    p.add_argument("--source-url", help="original source metadata when --file is used")
    p.add_argument("--label", required=True, help="human-readable rendition identifier")
    p.add_argument("--transcript-file", type=Path, help="optional existing lawful transcript, hashed but not copied")
    p.add_argument("--transcript-kind", choices=("verified-vtt", "supplied-vtt", "manual", "auto-captions", "unverified"))
    p.add_argument("--out", type=Path, help="optional JSON receipt destination; default stdout")
    p.add_argument("--max-bytes", type=int, default=MAX_BYTES)
    args = p.parse_args(argv)

    if args.max_bytes < 1:
        p.error("--max-bytes must be positive")
    if args.transcript_kind and not args.transcript_file:
        p.error("--transcript-kind needs --transcript-file")
    if args.transcript_file and not args.transcript_kind:
        p.error("--transcript-file needs --transcript-kind")
    if args.source_url and args.stream_url:
        p.error("source URL is already specified by --stream-url")

    if args.file:
        sha, size = digest_local(args.file, args.max_bytes)
        observed_url = args.source_url
        mode = "local_file"
    else:
        sha, size, observed_url = digest_https_media(args.stream_url, args.max_bytes)
        mode = "direct_https_stream"

    transcript = None
    if args.transcript_file:
        tsha, tsize = digest_local(args.transcript_file, args.max_bytes)
        transcript = {
            "sha256": tsha,
            "byte_count": tsize,
            "kind": args.transcript_kind,
            "aligned_to_video": False,
            "text_included": False,
        }

    result = {
        "schema_version": 1,
        "rendition_label": args.label,
        "collected_utc": datetime.now(timezone.utc).isoformat(),
        "mode": mode,
        "source_url": observed_url,
        "sha256": sha,
        "byte_count": size,
        "digest_scope": "exact rendition bytes, not original abstract film identity",
        "identity_with_doj_master_verified": False,
        "transcript": transcript,
        "media_bytes_embedded": False,
        "transcript_text_embedded": False,
    }
    serialized = json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(serialized, encoding="utf-8")
    else:
        sys.stdout.write(serialized)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as exc:
        print(f"media receipt failed: {exc}", file=sys.stderr)
        raise SystemExit(2) from exc
