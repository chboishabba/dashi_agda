#!/usr/bin/env python3
from __future__ import annotations

"""Deterministic local reference executor for the DASHI runtime vertical slice.

This is deliberately not a RabbitMQ/systemd implementation.  It gives the repo
one executable same-object path that:

  transition JSON -> canonical transition digest -> emitted event -> local state
  effect -> execution acknowledgement -> governed observation -> receipt.

The Kagenti/RabbitMQ adapter can later replace the local executor while retaining
the same transition identity and receipt schema.
"""

import argparse
import copy
import hashlib
import json
import pathlib
import sys
from typing import Any

SCHEMA = "dashi.runtime.vertical.v1"
VALID_KINDS = {"Created", "Updated", "Deleted"}


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def load_json(path: pathlib.Path) -> Any:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def transition_core(raw: dict[str, Any]) -> dict[str, Any]:
    missing = [key for key in ("kind", "name", "namespace", "payload") if key not in raw]
    if missing:
        raise ValueError(f"missing transition fields: {', '.join(missing)}")
    if raw["kind"] not in VALID_KINDS:
        raise ValueError(f"unsupported kind: {raw['kind']!r}")
    if not isinstance(raw["name"], str) or not raw["name"]:
        raise ValueError("name must be a non-empty string")
    if not isinstance(raw["namespace"], str) or not raw["namespace"]:
        raise ValueError("namespace must be a non-empty string")
    if not isinstance(raw["payload"], dict):
        raise ValueError("payload must be an object")
    return {
        "kind": raw["kind"],
        "name": raw["name"],
        "namespace": raw["namespace"],
        "payload": raw["payload"],
    }


def state_agents(state: dict[str, Any]) -> dict[str, Any]:
    agents = state.setdefault("agents", {})
    if not isinstance(agents, dict):
        raise ValueError("state.agents must be an object")
    return agents


def agent_key(namespace: str, name: str) -> str:
    return f"{namespace}/{name}"


def apply_transition(before: dict[str, Any], transition: dict[str, Any]) -> tuple[dict[str, Any], str]:
    after = copy.deepcopy(before)
    agents = state_agents(after)
    key = agent_key(transition["namespace"], transition["name"])
    kind = transition["kind"]

    if kind == "Created":
        if key in agents:
            raise ValueError(f"Created requires absent agent: {key}")
        agents[key] = copy.deepcopy(transition["payload"])
        return after, "created"

    if kind == "Updated":
        if key not in agents:
            raise ValueError(f"Updated requires existing agent: {key}")
        agents[key] = copy.deepcopy(transition["payload"])
        return after, "updated"

    if kind == "Deleted":
        if key not in agents:
            raise ValueError(f"Deleted requires existing agent: {key}")
        del agents[key]
        return after, "deleted"

    raise AssertionError("validated kind fell through")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("transition", type=pathlib.Path)
    parser.add_argument("state", type=pathlib.Path)
    parser.add_argument("receipt", type=pathlib.Path)
    args = parser.parse_args()

    try:
        raw = load_json(args.transition)
        if not isinstance(raw, dict):
            raise ValueError("transition root must be an object")
        transition = transition_core(raw)
        before = load_json(args.state)
        if not isinstance(before, dict):
            raise ValueError("state root must be an object")

        transition_canonical = canonical_json(transition)
        transition_id = sha256_text(transition_canonical)
        before_canonical = canonical_json(before)
        before_digest = sha256_text(before_canonical)

        after, effect = apply_transition(before, transition)
        after_canonical = canonical_json(after)
        after_digest = sha256_text(after_canonical)

        event = {
            "schema": SCHEMA,
            "exchange": "kagenti.events",
            "queue": "kagenti.agent.events",
            "transition_id": transition_id,
            "kind": transition["kind"],
            "name": transition["name"],
            "namespace": transition["namespace"],
            "payload": transition["payload"],
            "proof_receipt_id": raw.get("proof_receipt_id", "unbound-proof-receipt"),
            "authority_receipt_id": raw.get("authority_receipt_id", "unbound-authority-receipt"),
        }
        event_digest = sha256_text(canonical_json(event))

        receipt = {
            "schema": SCHEMA,
            "canonicalization": "python-json-sort-keys-compact-utf8-v1",
            "digest_algorithm": "sha256",
            "transition": transition,
            "transition_id": transition_id,
            "before_state": before,
            "before_state_digest": before_digest,
            "emitted_event": event,
            "emitted_event_digest": event_digest,
            "execution_ack": {
                "executed_transition_id": transition_id,
                "outcome": "runtimeExecuted",
                "executor": "deterministic-local-reference-executor",
                "external_effect": effect,
            },
            "after_state": after,
            "after_state_digest": after_digest,
            "governed_observation": {
                "observed_transition_id": transition_id,
                "observed_state_digest": after_digest,
                "changed_artifact": agent_key(transition["namespace"], transition["name"]),
                "residual": "runtime side effect observed; external RabbitMQ/Nix/systemd delivery remains unproven",
            },
        }

        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        args.state.write_text(json.dumps(after, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"runtime vertical slice failed: {exc}", file=sys.stderr)
        return 2

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
