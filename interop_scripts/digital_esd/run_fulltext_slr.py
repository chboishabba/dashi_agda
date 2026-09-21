#!/usr/bin/env python3
"""Run the existing SLR full-text parser over retained Digital-ESD studies.

Input:
  P0-G slr-source-unit-adapter.jsonl

This wrapper intentionally treats the historical Python SLR batch as an
execution adapter, not the production semantic ABI. Its outputs remain
candidate-only and non-promoting.

The wrapper verifies:
  - every input source unit produces exactly one manifest row;
  - input revision/source-unit references survive;
  - no output claims semantic promotion;
  - output files/manifests are hashed for replay/audit.

It does not create SourceAuditAdmission or a screening decision.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows = []
    with path.open("r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{n}: expected object")
            rows.append(row)
    return rows


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--input",
        required=True,
        type=Path,
        help="P0-G slr-source-unit-adapter.jsonl",
    )
    ap.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    ap.add_argument(
        "--out-dir",
        type=Path,
        default=Path("artifacts/digital-esd/slr-fulltext"),
    )
    ap.add_argument(
        "--spacy-model",
        help="optional spaCy model forwarded to the existing SLR batch if supported",
    )
    args = ap.parse_args()

    repo = args.repo_root.resolve()
    input_path = args.input.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    source_units = read_jsonl(input_path)
    if not source_units:
        raise RuntimeError("no full-text source units supplied")

    for row in source_units:
        if row.get("adapter_is_production_semantic_abi") is not False:
            raise RuntimeError(
                "full-text adapter input must explicitly remain non-production ABI"
            )
        for key in ("source_unit_ref", "revision_ref", "text_path"):
            if not str(row.get(key) or "").strip():
                raise RuntimeError(
                    f"{row.get('source_unit_ref', '<unknown>')}: missing {key}"
                )
        text_path = Path(str(row["text_path"]))
        if not text_path.is_absolute():
            text_path = (repo / text_path).resolve()
        if not text_path.exists():
            raise FileNotFoundError(
                f"{row['source_unit_ref']}: text_path missing: {text_path}"
            )

    parser = repo / "tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py"
    if not parser.exists():
        raise FileNotFoundError(
            "existing SLR source-unit parser not found at "
            "tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py"
        )

    records_dir = out_dir / "records"
    manifest = out_dir / "slr-manifest.jsonl"
    summary = out_dir / "slr-summary.json"

    cmd = [
        sys.executable,
        str(parser),
        "--input-jsonl",
        str(input_path),
        "--output-dir",
        str(records_dir),
        "--manifest",
        str(manifest),
        "--summary",
        str(summary),
    ]
    if args.spacy_model:
        cmd.extend(["--spacy-model", args.spacy_model])

    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=repo, check=True)

    manifest_rows = read_jsonl(manifest)
    if len(manifest_rows) != len(source_units):
        raise RuntimeError(
            "SLR denominator mismatch: "
            f"inputs={len(source_units)} manifest_rows={len(manifest_rows)}"
        )

    input_by_ref = {str(row["source_unit_ref"]): row for row in source_units}
    output_refs: set[str] = set()
    for row in manifest_rows:
        ref = str(
            row.get("source_unit_ref")
            or row.get("source_ref")
            or row.get("sourceUnitRef")
            or ""
        )
        if not ref:
            raise RuntimeError("SLR manifest row lacks source_unit_ref")
        if ref not in input_by_ref:
            raise RuntimeError(f"SLR output source unit not present in input: {ref}")
        if ref in output_refs:
            raise RuntimeError(f"duplicate SLR output source unit: {ref}")
        output_refs.add(ref)

        candidate_only = row.get("candidate_only")
        semantic_promotion = row.get("semantic_promotion")
        if candidate_only is not True:
            raise RuntimeError(f"{ref}: SLR output lost candidate_only=true")
        if semantic_promotion not in (False, None):
            raise RuntimeError(f"{ref}: SLR output claims semantic promotion")

        in_revision = str(input_by_ref[ref]["revision_ref"])
        out_revision = str(
            row.get("revision_ref")
            or row.get("source_revision_ref")
            or row.get("revisionRef")
            or ""
        )
        if out_revision and out_revision != in_revision:
            raise RuntimeError(
                f"{ref}: revision drift input={in_revision} output={out_revision}"
            )

    missing = sorted(set(input_by_ref) - output_refs)
    if missing:
        raise RuntimeError(
            "SLR outputs missing source units: " + ", ".join(missing[:20])
        )

    receipt = {
        "schema": "digital-esd-fulltext-slr-execution-v1",
        "execution_adapter": str(parser.relative_to(repo)),
        "execution_adapter_is_production_semantic_abi": False,
        "input_reference": str(input_path),
        "input_sha256": sha256_file(input_path),
        "input_source_unit_count": len(source_units),
        "output_manifest_reference": str(manifest),
        "output_manifest_sha256": sha256_file(manifest),
        "output_manifest_count": len(manifest_rows),
        "summary_reference": str(summary),
        "summary_sha256": sha256_file(summary),
        "records_dir": str(records_dir),
        "all_source_units_accounted_for": True,
        "candidate_only": True,
        "semantic_promotion": False,
        "creates_screening_decision": False,
        "creates_source_audit_admission": False,
    }
    receipt_path = out_dir / "digital-esd-slr-execution-receipt.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
