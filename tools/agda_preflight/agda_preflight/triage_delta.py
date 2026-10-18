from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from .triage_render import TriageReport, _cause_groups, _cause_label, _code_label


def _stable_path(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except (ValueError, OSError):
        return str(path)


def _signature(path: str, cause_key: tuple[str, ...]) -> str:
    payload = json.dumps([path, *cause_key], ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:20]


def triage_snapshot(report: TriageReport) -> dict[str, Any]:
    causes = []
    for group in _cause_groups(report.logical):
        first = group[0]
        path = _stable_path(first.path, report.root)
        causes.append(
            {
                "signature": _signature(path, first.cause_key),
                "path": path,
                "kind": first.kind,
                "label": _cause_label(group),
                "codes": _code_label(group),
                "count": len(group),
                "raw_diagnostics": sum(len(item.diagnostics) for item in group),
            }
        )
    causes.sort(key=lambda item: (item["path"], item["kind"], item["label"]))
    return {
        "schema": "dashi-agda-preflight-triage-v1",
        "fingerprint": report.fingerprint,
        "root_causes": causes,
    }


def _safe_count(item) -> int:
    if not isinstance(item, dict):
        return 0
    try:
        return int(item.get("count", 0))
    except (TypeError, ValueError):
        return 0


def render_delta(previous: dict[str, Any], current: TriageReport) -> str:
    if not isinstance(previous, dict):
        previous = {}
    current_snapshot = triage_snapshot(current)
    if previous.get("fingerprint") == current_snapshot["fingerprint"]:
        return f"Δ since previous run: no diagnostic changes ({current.fingerprint})"

    old = {
        item["signature"]: item
        for item in previous.get("root_causes", [])
        if isinstance(item, dict) and item.get("signature")
    }
    new = {item["signature"]: item for item in current_snapshot["root_causes"]}
    rows = []
    for signature in sorted(set(old) | set(new)):
        before = old.get(signature)
        after = new.get(signature)
        before_count = _safe_count(before)
        after_count = _safe_count(after)
        delta = after_count - before_count
        if delta == 0:
            continue
        item = after or before
        rows.append(
            (
                delta,
                item.get("path", ""),
                item.get("label", "diagnostic"),
                item.get("codes", ""),
            )
        )

    output = ["Δ since previous run"]
    if not rows:
        output.append("  fingerprint changed, but root-cause counts are unchanged")
    else:
        for delta, path, label, codes in sorted(rows, key=lambda row: (row[1], row[2], row[0])):
            output.append(f"  {delta:+d}  {label}  {codes}  {path}")
    output.append(f"  fingerprint: {previous.get('fingerprint', '<unknown>')} → {current.fingerprint}")
    return "\n".join(output)
