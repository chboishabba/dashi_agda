#!/usr/bin/env python3
from __future__ import annotations

"""Replay and verify a DASHI runtime vertical-slice receipt."""

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


def agent_key(namespace: str, name: str) -> str:
    return f"{namespace}/{name}"


def apply_transition(before: dict[str, Any], transition: dict[str, Any]) -> dict[str, Any]:
    after = copy.deepcopy(before)
    agents = after.setdefault("agents", {})
    if not isinstance(agents, dict):
        raise ValueError("state.agents must be an object")

    kind = transition["kind"]
    if kind not in VALID_KINDS:
        raise ValueError(f"unsupported kind: {kind!r}")
    key = agent_key(transition["namespace"], transition["name"])

    if kind == "Created":
        if key in agents:
            raise ValueError(f"Created requires absent agent: {key}")
        agents[key] = copy.deepcopy(transition["payload"])
    elif kind == "Updated":
        if key not in agents:
            raise ValueError(f"Updated requires existing agent: {key}")
        agents[key] = copy.deepcopy(transition["payload"])
    elif kind == "Deleted":
        if key not in agents:
            raise ValueError(f"Deleted requires existing agent: {key}")
        del agents[key]
    return after


def fail(message: str) -> None:
    raise ValueError(message)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("receipt", type=pathlib.Path)
    args = parser.parse_args()

    try:
        receipt = json.loads(args.receipt.read_text(encoding="utf-8"))
        if receipt.get("schema") != SCHEMA:
            fail("unexpected receipt schema")

        transition = receipt["transition"]
        before = receipt["before_state"]
        after = receipt["after_state"]
        event = receipt["emitted_event"]
        ack = receipt["execution_ack"]
        observation = receipt["governed_observation"]

        transition_id = sha256_text(canonical_json(transition))
        if receipt.get("transition_id") != transition_id:
            fail("transition digest mismatch")
        if event.get("transition_id") != transition_id:
            fail("emitted event is not tied to the certified transition")
        if ack.get("executed_transition_id") != transition_id:
            fail("execution ack is not tied to the certified transition")
        if observation.get("observed_transition_id") != transition_id:
            fail("feedback observation is not tied to the certified transition")

        if event.get("kind") != transition.get("kind"):
            fail("event kind differs from transition kind")
        if event.get("name") != transition.get("name"):
            fail("event name differs from transition name")
        if event.get("namespace") != transition.get("namespace"):
            fail("event namespace differs from transition namespace")
        if event.get("payload") != transition.get("payload"):
            fail("event payload differs from transition payload")

        expected_event_digest = sha256_text(canonical_json(event))
        if receipt.get("emitted_event_digest") != expected_event_digest:
            fail("emitted event digest mismatch")

        before_digest = sha256_text(canonical_json(before))
        if receipt.get("before_state_digest") != before_digest:
            fail("before-state digest mismatch")

        replayed_after = apply_transition(before, transition)
        if replayed_after != after:
            fail("replay result differs from recorded after-state")

        after_digest = sha256_text(canonical_json(after))
        if receipt.get("after_state_digest") != after_digest:
            fail("after-state digest mismatch")
        if observation.get("observed_state_digest") != after_digest:
            fail("feedback observation does not identify the recorded after-state")

        expected_changed = agent_key(transition["namespace"], transition["name"])
        if observation.get("changed_artifact") != expected_changed:
            fail("changed-artifact reference differs from executed transition")

        if ack.get("outcome") != "runtimeExecuted":
            fail("reference fixture must carry runtimeExecuted outcome")

    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"runtime receipt verification failed: {exc}", file=sys.stderr)
        return 2

    print("runtime vertical-slice receipt verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
