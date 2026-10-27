#!/usr/bin/env python3

from __future__ import annotations

import argparse
import csv
import re

from pathlib import Path


POSTULATE_RE = re.compile(r"\bpostulate\b")
HOLE_RE = re.compile(r"\?|\{!!\}|TODO|FIXME")
TRIVIAL_RE = re.compile(r"^\s*(refl|tt|zero|suc|true|false)\s*$")


def score_text(text: str):
    # Conservative heuristic only. This ranks review priority; it does not
    # prove that one Agda proof is logically stronger than another.
    return {
        "postulate_tokens": len(POSTULATE_RE.findall(text)),
        "hole_markers": len(HOLE_RE.findall(text)),
        "trivial_body": int(bool(TRIVIAL_RE.match(text or ""))),
        "text_length": len(text),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--candidates",
        default=".dashi/round-stranded/stranded-candidates.csv",
    )
    ap.add_argument("--root", default=".")
    ap.add_argument(
        "--out",
        default=".dashi/round-stranded/proof-review-queue.csv",
    )
    args = ap.parse_args()

    rows = list(csv.DictReader(open(args.candidates, encoding="utf-8")))
    root = Path(args.root)
    output = []

    for row in rows:
        path = root / row["leaf_file"]
        text = (
            path.read_text(encoding="utf-8", errors="replace")
            if path.exists()
            else ""
        )
        quality = score_text(text)
        priority = 0

        if row["classification"] in {
            "stranded_signature",
            "stranded_proof_change",
        }:
            priority += 50
        if row["classification"] == "canonical_name_collision":
            priority += 40
        if row["classification"] in {
            "alternate_proof",
            "alternate_implementation",
        }:
            priority += 20

        priority += min(quality["postulate_tokens"], 20) * 2
        priority += min(quality["hole_markers"], 20) * 3

        output.append(
            {
                **row,
                **quality,
                "review_priority": priority,
            }
        )

    output.sort(
        key=lambda x: (
            -int(x["review_priority"]),
            x["leaf_module"],
            x["name"],
        )
    )

    Path(args.out).parent.mkdir(parents=True, exist_ok=True)

    if output:
        with open(args.out, "w", newline="", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=output[0].keys())
            writer.writeheader()
            writer.writerows(output)

    print(f"wrote {len(output)} rows to {args.out}")


if __name__ == "__main__":
    main()
