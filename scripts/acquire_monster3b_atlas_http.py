#!/usr/bin/env python3
"""Acquire the Monster-3B normalizer matrix inputs directly from ATLAS HTML.

This is a network acquisition helper, not theorem evidence.  It removes the
local GAP+AtlasRep requirement from the source-data step by starting at the two
canonical ATLAS representation pages already pinned by the Agda source receipt:

  2Suzd2G1-f3r12aB0   -- 12-dimensional GF(3) representation of 2.Suz:2
  M3max7G0-f3r38B0    -- 38-dimensional GF(3) Monster-normalizer representation

The script discovers downloadable matrix links from the pages rather than
hard-coding an undocumented download directory, saves the bytes, and emits a
SHA-256 manifest.  The downstream symplectic-form/basis/cocycle analyzer must
still validate the parsed matrices before any same-basis recognition is paid.
"""
from __future__ import annotations

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
from urllib.parse import urljoin
from urllib.request import Request, urlopen

BASE = "https://brauer.maths.qmul.ac.uk/Atlas/v3/matrep/"
REPRESENTATIONS = {
    "direct12": "2Suzd2G1-f3r12aB0",
    "monster38": "M3max7G0-f3r38B0",
}


class LinkParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag, attrs):
        if tag.lower() != "a":
            return
        href = dict(attrs).get("href")
        if href:
            self.links.append(href)


def fetch(url: str) -> bytes:
    req = Request(url, headers={"User-Agent": "DASHI-ATLAS-acquisition/1.0"})
    with urlopen(req, timeout=60) as response:
        return response.read()


def discover(rep_id: str) -> tuple[str, list[str]]:
    page_url = urljoin(BASE, rep_id)
    html = fetch(page_url).decode("utf-8", errors="replace")
    parser = LinkParser()
    parser.feed(html)
    links = [urljoin(page_url, h) for h in parser.links]

    # Prefer literal ATLAS generator-file names when exposed.  Otherwise retain
    # GAP-format download links from the canonical representation page.
    literal = [u for u in links if any(f"{rep_id}.m{i}" in u for i in range(1, 6))]
    if literal:
        return page_url, sorted(set(literal))
    gapish = [u for u in links if "gap" in u.lower() or "download" in u.lower()]
    if not gapish:
        raise RuntimeError(f"no matrix/GAP download links discovered on {page_url}")
    return page_url, sorted(set(gapish))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", default="data/monster3b_atlas")
    args = ap.parse_args()
    out = Path(args.outdir)
    out.mkdir(parents=True, exist_ok=True)

    manifest = {
        "authority": "ATLAS of Group Representations",
        "base": BASE,
        "representations": {},
        "same_basis_recognition_paid": False,
    }
    for role, rep_id in REPRESENTATIONS.items():
        page_url, urls = discover(rep_id)
        files = []
        for n, url in enumerate(urls, 1):
            payload = fetch(url)
            name = url.rstrip("/").split("/")[-1] or f"{rep_id}-download-{n}"
            target = out / name
            target.write_bytes(payload)
            files.append({
                "url": url,
                "path": str(target),
                "bytes": len(payload),
                "sha256": hashlib.sha256(payload).hexdigest(),
            })
        manifest["representations"][role] = {
            "representation_id": rep_id,
            "page_url": page_url,
            "files": files,
        }

    manifest_path = out / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
