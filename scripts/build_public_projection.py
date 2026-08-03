#!/usr/bin/env python3
"""Build a public JSON projection from a fully classified source document.

This is a compact reference implementation of the Agda disclosure boundary.
It is not an encryption, consent, access-control, or irreversible-publication
solution.  The builder fails closed when a field is unclassified or an action
is unknown, and it refuses to silently remove the reserved attribution field.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

ALLOWED_ACTIONS = {
    "retain",
    "remove",
    "pseudonymise",
    "coarsen_location",
    "aggregate",
    "existence_claim",
    "controlled_summary",
}


class ProjectionError(ValueError):
    """Raised when a projection cannot be produced safely."""


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def apply_rule(field_name: str, value: Any, rule: dict[str, Any]) -> tuple[bool, Any]:
    action = rule.get("action")
    if action not in ALLOWED_ACTIONS:
        raise ProjectionError(f"unknown action for {field_name!r}: {action!r}")

    if field_name == "attribution" and action == "remove":
        raise ProjectionError("the attribution field cannot be silently removed")

    replacement = rule.get("replacement")

    if action == "retain":
        return True, value
    if action == "remove":
        return False, None
    if action == "pseudonymise":
        if replacement is None:
            raise ProjectionError(f"pseudonymise requires replacement for {field_name!r}")
        return True, replacement
    if action == "coarsen_location":
        if replacement is None:
            raise ProjectionError(f"coarsen_location requires replacement for {field_name!r}")
        return True, replacement
    if action == "aggregate":
        if replacement is None:
            raise ProjectionError(f"aggregate requires replacement for {field_name!r}")
        return True, replacement
    if action == "existence_claim":
        label = replacement or f"restricted {field_name} exists"
        return True, {"exists": True, "reading": label}
    if action == "controlled_summary":
        if replacement is None:
            raise ProjectionError(f"controlled_summary requires replacement for {field_name!r}")
        return True, replacement

    raise AssertionError("allowed action was not handled")


def build_projection(source: dict[str, Any], policy: dict[str, Any]) -> dict[str, Any]:
    records = source.get("records")
    rules = policy.get("rules")
    if not isinstance(records, list):
        raise ProjectionError("source.records must be a list")
    if not isinstance(rules, dict):
        raise ProjectionError("policy.rules must be an object")
    if policy.get("default", "reject") != "reject":
        raise ProjectionError("only the fail-closed default 'reject' is supported")

    projected_records: list[dict[str, Any]] = []
    actions_used: dict[str, str] = {}

    for index, record in enumerate(records):
        if not isinstance(record, dict):
            raise ProjectionError(f"record {index} must be an object")
        fields = record.get("fields")
        if not isinstance(fields, dict):
            raise ProjectionError(f"record {index}.fields must be an object")

        projected_fields: dict[str, Any] = {}
        for field_name, value in fields.items():
            rule = rules.get(field_name)
            if not isinstance(rule, dict):
                raise ProjectionError(f"unclassified field: {field_name!r}")
            keep, projected_value = apply_rule(field_name, value, rule)
            actions_used[field_name] = str(rule["action"])
            if keep:
                projected_fields[field_name] = projected_value

        projected_records.append(
            {
                "id": record.get("id", f"record-{index}"),
                "fields": projected_fields,
            }
        )

    artifact = {
        "artifact_label": policy.get("public_label", "public projection"),
        "records": projected_records,
        "withheld_residual": policy.get(
            "withheld_residual",
            "This public artifact is intentionally incomplete.",
        ),
    }
    artifact["publication_receipt"] = {
        "source_sha256": digest(source),
        "policy_sha256": digest(policy),
        "artifact_payload_sha256": digest(artifact),
        "actions_used": actions_used,
        "claims_complete_non_leakage": False,
        "claims_community_authority": False,
    }
    return artifact


def self_test() -> None:
    source = {
        "records": [
            {
                "id": "mole-example",
                "fields": {
                    "attribution": {
                        "author": "Named source",
                        "title": "Attributed work",
                    },
                    "location": "precise vulnerable location",
                    "ritual": "restricted interpretation",
                    "process": "precise process parameters",
                },
            }
        ]
    }
    policy = {
        "default": "reject",
        "public_label": "self-test projection",
        "withheld_residual": "restricted detail remains withheld",
        "rules": {
            "attribution": {"action": "retain"},
            "location": {
                "action": "coarsen_location",
                "replacement": "region withheld",
            },
            "ritual": {
                "action": "existence_claim",
                "replacement": "a restricted interpretation exists",
            },
            "process": {
                "action": "controlled_summary",
                "replacement": "order-sensitive culinary process",
            },
        },
    }
    artifact = build_projection(source, policy)
    fields = artifact["records"][0]["fields"]
    assert fields["attribution"]["author"] == "Named source"
    assert fields["location"] == "region withheld"
    assert fields["ritual"]["exists"] is True
    assert fields["process"] == "order-sensitive culinary process"
    assert artifact["publication_receipt"]["claims_complete_non_leakage"] is False

    bad_policy = {
        "default": "reject",
        "rules": {"attribution": {"action": "remove"}},
    }
    try:
        build_projection(
            {"records": [{"fields": {"attribution": "source"}}]},
            bad_policy,
        )
    except ProjectionError:
        pass
    else:
        raise AssertionError("attribution removal did not fail closed")

    print("public projection self-test passed")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", nargs="?", type=Path)
    parser.add_argument("policy", nargs="?", type=Path)
    parser.add_argument("output", nargs="?", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return 0

    if args.source is None or args.policy is None or args.output is None:
        parser.error("source, policy, and output are required unless --self-test is used")

    try:
        source = json.loads(args.source.read_text(encoding="utf-8"))
        policy = json.loads(args.policy.read_text(encoding="utf-8"))
        artifact = build_projection(source, policy)
        args.output.write_text(
            json.dumps(artifact, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except (OSError, json.JSONDecodeError, ProjectionError) as exc:
        parser.exit(1, f"public projection failed: {exc}\n")

    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
