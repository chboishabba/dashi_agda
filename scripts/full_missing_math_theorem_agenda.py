#!/usr/bin/env python3
"""Aggregate the exact NS/YM/UCT missing-theorem agendas.

This is an integration surface only. It does not restate theorem truth; it
loads each domain agenda, normalizes row identity/metadata, and keeps every
promotion gate closed.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

DOMAIN_SCRIPTS = {
    "NS": SCRIPT_DIR / "ns_missing_math_theorem_agenda.py",
    "YM": SCRIPT_DIR / "ym_missing_math_theorem_agenda.py",
    "UCT": SCRIPT_DIR / "uct_missing_math_theorem_agenda.py",
}

EXPECTED_COUNTS = {
    "NS": 5,
    "YM": 5,
    "UCT": 8,
}

EXPECTED_THEOREM_IDS = {
    "NS": ("NS-A", "NS-B", "NS-C", "NS-D", "NS-E"),
    "YM": ("YM-A", "YM-B", "YM-C", "YM-D", "YM-E"),
    "UCT": ("UCT-A", "UCT-B", "UCT-C", "UCT-D", "UCT-E", "UCT-F", "UCT-G", "UCT-H"),
}

PROMOTION_KEYS = (
    "promotion_allowed",
    "clay_promotion",
    "terminal_promotion",
)

THEOREM_LIST_KEYS = (
    "targets",
    "theorem_targets",
    "theorems",
    "missing_theorems",
    "theorem_agenda",
    "agenda",
    "items",
    "rows",
    "tasks",
    "obligations",
)


class AgendaError(RuntimeError):
    """Raised when a domain agenda cannot be loaded or normalized."""


def load_domain_payload(domain: str, path: Path) -> dict[str, Any]:
    if not path.exists():
        raise AgendaError(f"{domain}: missing domain surface {path.relative_to(REPO_ROOT)}")

    result = subprocess.run(
        [sys.executable, str(path), "--format", "json"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise AgendaError(f"{domain}: domain surface failed: {detail}")

    try:
        payload = json.loads(result.stdout)
    except json.JSONDecodeError as exc:
        raise AgendaError(f"{domain}: malformed JSON from {path.name}: {exc}") from exc

    if not isinstance(payload, dict):
        raise AgendaError(f"{domain}: domain surface must emit a JSON object")
    return payload


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for item in value.values():
            yield from walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from walk(item)


def first_present(row: dict[str, Any], keys: tuple[str, ...]) -> Any:
    for key in keys:
        if key in row:
            return row[key]
    return None


def string_list(value: Any, *, field: str, theorem_id: str) -> list[str]:
    if value is None:
        return []
    if isinstance(value, str):
        return [value]
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return [*value]
    raise AgendaError(f"{theorem_id}: {field} must be a string list")


def is_false(value: Any) -> bool:
    return value is False or (isinstance(value, str) and value.lower() == "false")


def is_nonpromoting_status(status: str) -> bool:
    lowered = status.lower().replace("-", "_").replace(" ", "_")
    negative_markers = (
        "not_proved",
        "unproved",
        "false",
        "fail_closed",
        "blocked",
        "locked",
        "open",
        "boundary",
        "authority_intake",
        "diagnostic",
        "target",
    )
    if any(marker in lowered for marker in negative_markers):
        return True
    return not any(word in lowered for word in ("proved", "promoted", "complete", "terminal"))


def assert_no_positive_promotion(domain: str, value: Any) -> None:
    positives: list[str] = []
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        for key, flag in item.items():
            key_lower = key.lower()
            if "promotion" not in key_lower and "promoted" not in key_lower:
                continue
            if flag is True:
                positives.append(key)
            if isinstance(flag, str) and flag.lower() in {"true", "promoted", "allowed"}:
                positives.append(key)
    if positives:
        joined = ", ".join(sorted(set(positives)))
        raise AgendaError(f"{domain}: positive promotion flags are forbidden: {joined}")


def candidate_lists(payload: dict[str, Any], domain: str) -> list[list[Any]]:
    lists: list[list[Any]] = []

    for key in THEOREM_LIST_KEYS:
        value = payload.get(key)
        if isinstance(value, list):
            lists.append(value)

    domains = payload.get("domains")
    if isinstance(domains, dict):
        domain_payload = domains.get(domain) or domains.get(domain.lower())
        if isinstance(domain_payload, dict):
            for key in THEOREM_LIST_KEYS:
                value = domain_payload.get(key)
                if isinstance(value, list):
                    lists.append(value)

    walls = payload.get("walls")
    if isinstance(walls, dict):
        value = walls.get(domain) or walls.get(domain.lower())
        if isinstance(value, list):
            lists.append(value)

    return lists


def has_theorem_identity(row: Any) -> bool:
    if not isinstance(row, dict):
        return False
    return any(key in row for key in ("theorem_id", "id", "task_id", "obligation_id", "slug"))


def extract_theorem_rows(domain: str, payload: dict[str, Any]) -> list[dict[str, Any]]:
    candidates = [
        rows
        for rows in candidate_lists(payload, domain)
        if rows and all(has_theorem_identity(row) for row in rows)
    ]
    if not candidates:
        raise AgendaError(f"{domain}: no theorem list found")

    expected = EXPECTED_COUNTS[domain]
    exact = [rows for rows in candidates if len(rows) == expected]
    selected = exact[0] if exact else candidates[0]
    if len(selected) != expected:
        raise AgendaError(f"{domain}: expected {expected} theorems, found {len(selected)}")

    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for raw in selected:
        assert isinstance(raw, dict)
        theorem_id = first_present(raw, ("theorem_id", "id", "task_id", "obligation_id", "slug"))
        if not isinstance(theorem_id, str) or not theorem_id:
            raise AgendaError(f"{domain}: theorem row has missing theorem id")
        if theorem_id in seen:
            raise AgendaError(f"{domain}: duplicate theorem id {theorem_id}")
        seen.add(theorem_id)

        title = first_present(raw, ("title", "name", "theorem_name", "label", "theorem", "claim"))
        if not isinstance(title, str) or not title:
            raise AgendaError(f"{domain}:{theorem_id}: missing theorem title")

        status = first_present(raw, ("status", "state", "disposition"))
        if not isinstance(status, str) or not status:
            raise AgendaError(f"{domain}:{theorem_id}: missing theorem status")
        if not is_nonpromoting_status(status):
            raise AgendaError(f"{domain}:{theorem_id}: promoting status is forbidden: {status}")

        support = first_present(raw, ("support", "support_files", "primary_support_files", "files"))
        depends_on = first_present(raw, ("depends_on", "dependencies", "blocked_by"))
        missing = first_present(raw, ("missing_content", "missing", "gap", "blocker", "obligation"))

        for key in PROMOTION_KEYS:
            if key in raw and not is_false(raw[key]):
                raise AgendaError(f"{domain}:{theorem_id}: {key} must be false")

        normalized.append(
            {
                "domain": domain,
                "theorem_id": theorem_id,
                "title": title,
                "status": status,
                "missing_content": missing if isinstance(missing, str) else "",
                "depends_on": string_list(depends_on, field="depends_on", theorem_id=theorem_id),
                "support": string_list(support, field="support", theorem_id=theorem_id),
                "promotion_allowed": False,
                "clay_promotion": False,
                "terminal_promotion": False,
            }
        )
    return normalized


def build_packet() -> dict[str, Any]:
    domains: dict[str, Any] = {}
    all_theorems: list[dict[str, Any]] = []

    for domain, path in DOMAIN_SCRIPTS.items():
        payload = load_domain_payload(domain, path)
        assert_no_positive_promotion(domain, payload)
        theorems = extract_theorem_rows(domain, payload)
        domains[domain] = {
            "source_script": str(path.relative_to(REPO_ROOT)),
            "count": len(theorems),
            "theorems": theorems,
        }
        all_theorems.extend(theorems)

    counts = {domain: domains[domain]["count"] for domain in DOMAIN_SCRIPTS}
    if counts != EXPECTED_COUNTS:
        raise AgendaError(f"exact theorem counts mismatch: expected {EXPECTED_COUNTS}, found {counts}")

    ids_by_domain = {
        domain: tuple(row["theorem_id"] for row in domains[domain]["theorems"])
        for domain in DOMAIN_SCRIPTS
    }
    if ids_by_domain != EXPECTED_THEOREM_IDS:
        raise AgendaError(f"exact theorem ids mismatch: expected {EXPECTED_THEOREM_IDS}, found {ids_by_domain}")

    ids = [row["theorem_id"] for row in all_theorems]
    if len(ids) != len(set(ids)):
        raise AgendaError("duplicate theorem ids across domains")

    return {
        "schema": "full_missing_math_theorem_agenda.v1",
        "fail_closed": True,
        "promotion_allowed": False,
        "clay_promotion": False,
        "terminal_promotion": False,
        "counts_by_domain": counts,
        "expected_counts": {**EXPECTED_COUNTS},
        "expected_theorem_ids": {domain: [*ids] for domain, ids in EXPECTED_THEOREM_IDS.items()},
        "total_theorems": len(all_theorems),
        "domains": domains,
        "theorems": all_theorems,
    }


def render_md(packet: dict[str, Any]) -> str:
    lines = [
        "# Full Missing Math Theorem Agenda",
        "",
        f"- fail_closed: {str(packet['fail_closed']).lower()}",
        f"- promotion_allowed: {str(packet['promotion_allowed']).lower()}",
        f"- clay_promotion: {str(packet['clay_promotion']).lower()}",
        f"- terminal_promotion: {str(packet['terminal_promotion']).lower()}",
        f"- total_theorems: {packet['total_theorems']}",
        "",
        "## Counts",
        "",
        "| Domain | Count | Expected |",
        "| --- | ---: | ---: |",
    ]
    counts = packet["counts_by_domain"]
    expected = packet["expected_counts"]
    for domain in DOMAIN_SCRIPTS:
        lines.append(f"| {domain} | {counts[domain]} | {expected[domain]} |")

    for domain in DOMAIN_SCRIPTS:
        lines.extend(["", f"## {domain}", "", "| Theorem ID | Status | Title |", "| --- | --- | --- |"])
        for row in packet["domains"][domain]["theorems"]:
            lines.append(f"| {row['theorem_id']} | {row['status']} | {row['title']} |")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("json", "md"), default="json")
    args = parser.parse_args(argv)

    try:
        packet = build_packet()
    except AgendaError as exc:
        print(f"full_missing_math_theorem_agenda: {exc}", file=sys.stderr)
        return 2

    if args.format == "json":
        print(json.dumps(packet, indent=2, sort_keys=True))
    else:
        print(render_md(packet), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
