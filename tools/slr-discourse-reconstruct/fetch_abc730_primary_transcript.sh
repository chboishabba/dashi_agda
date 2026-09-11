#!/usr/bin/env bash
set -euo pipefail

URL="${1:-https://www.abc.net.au/news/2026-09-09/new-sanctions-placed-on-israeli-settlements-/107135268}"
OUT="${2:-$(dirname "$0")/specimens/abc730-2026-09-09-primary}"
mkdir -p "$OUT"

python3 - "$URL" "$OUT" <<'PY'
from __future__ import annotations
from html.parser import HTMLParser
from pathlib import Path
from urllib.request import Request, urlopen
import hashlib, html, json, re, sys

url = sys.argv[1]
out = Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
req = Request(url, headers={"User-Agent": "dashi-slr-source-acquisition/1.1 (+research; public ABC transcript)"})
with urlopen(req, timeout=30) as r:
    raw = r.read()
    final_url = r.geturl()

page = out / "source-page.html"
page.write_bytes(raw)
text = raw.decode("utf-8", errors="replace")

class Blocks(HTMLParser):
    BLOCKS = {"h1","h2","h3","h4","p"}
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack=[]
        self.blocks=[]
    def handle_starttag(self, tag, attrs):
        if tag in self.BLOCKS:
            self.stack.append([tag, []])
    def handle_data(self, data):
        for item in self.stack:
            item[1].append(data)
    def handle_endtag(self, tag):
        for i in range(len(self.stack)-1, -1, -1):
            if self.stack[i][0] == tag:
                t, buf = self.stack.pop(i)
                s = re.sub(r"\s+", " ", "".join(buf)).strip()
                if s:
                    self.blocks.append((t, html.unescape(s)))
                break

p = Blocks(); p.feed(text)
start = None
for i,(tag,s) in enumerate(p.blocks):
    if tag in {"h2","h3"} and s.strip().lower() == "transcript":
        start = i + 1
        break
if start is None:
    raise SystemExit("ERROR: could not locate Transcript heading in fetched ABC page")

lines=[]
for tag,s in p.blocks[start:]:
    if tag in {"h1","h2"}:
        break
    if tag == "p":
        s=s.strip()
        if s:
            lines.append(s)
            if s.startswith("EMILY THORNBERRY:") and "not at all" in s.lower():
                break
if not lines:
    raise SystemExit("ERROR: Transcript heading found but no transcript paragraphs extracted")

transcript = "\n\n".join(lines).strip() + "\n"
transcript_path = out / "source.txt"
transcript_path.write_text(transcript, encoding="utf-8")

def sha256(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

transcript_sha = sha256(transcript.encode("utf-8"))
meta = {
    "schema": "abc730-primary-transcript-source-v2",
    "title": "New sanctions placed on Israeli settlements",
    "publisher": "ABC News / 7.30",
    "published_date": "2026-09-09",
    "requested_url": url,
    "resolved_url": final_url,
    "page_sha256": sha256(raw),
    "transcript_sha256": transcript_sha,
    "transcript_paragraphs": len(lines),
    "source_role": "speaker-labelled primary programme transcript",
    "source_role_by_claim": {
        "primary_for": [
            "speaker labels",
            "utterance wording",
            "interview questions",
            "public policy positions as stated",
            "speaker-attributed evaluative rhetoric"
        ],
        "not_automatically_primary_for": [
            "underlying reported events",
            "independent legal truth",
            "casualty or perpetrator attribution",
            "causal policy effectiveness",
            "predicted consequences"
        ]
    },
    "ibrahim": {
        "dewey_parent": "327",
        "dewey_role": "retrieval-coordinate-only",
        "doi": {
            "state": "no-doi-observed-on-this-source-object",
            "scope": "atlas-local; do not infer global nonexistence"
        },
        "stable_source_id": f"abc730-2026-09-09:{transcript_sha}",
        "qid_role": "external-identity-coordinate-only",
        "verified_qids": {
            "Australian Broadcasting Corporation": "Q781365",
            "ABC News": "Q4650197",
            "7.30": "Q4642897",
            "Penny Wong": "Q456759",
            "Ed Husic": "Q5334974",
            "David Shoebridge": "Q5239754",
            "Julian Leeser": "Q24191457",
            "Emily Thornberry": "Q272408",
            "Sarah Ferguson": "Q17004206"
        },
        "unresolved_qids": ["Jacob Greber"],
        "acquisition_order_can_be_opportunistic": True,
        "payment_order_requires_same_object_and_claim_role_weld": True
    },
    "semantic_promotion": False,
}
(out / "source.json").write_text(json.dumps(meta, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")
(out / "source.sha256").write_text(f"{meta['transcript_sha256']}  source.txt\n", encoding="utf-8")
print("ABC730_PRIMARY_TRANSCRIPT_RECEIPT " + " ".join([
    f"schema={meta['schema']}",
    f"paragraphs={len(lines)}",
    f"page_sha256={meta['page_sha256']}",
    f"transcript_sha256={meta['transcript_sha256']}",
    f"out={out}",
    "speaker_labels_preserved=true",
    "ibrahim_coordinates=true",
    "claim_relative_primaryness=true",
    "semantic_promotion=false",
]))
PY

printf 'source=%s\nmetadata=%s\npage=%s\n' "$OUT/source.txt" "$OUT/source.json" "$OUT/source-page.html"
