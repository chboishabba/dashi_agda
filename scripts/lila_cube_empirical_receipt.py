#!/usr/bin/env python3
"""Validate a candidate LILA hidden->cube same-object empirical receipt.

Input JSON schema:
{
  "rows": [
    {"id":"t0", "next_id":"t1", "split":"train|heldout",
     "cube":[27 trits 0..2],
     "hidden_consumer": <JSON value>, "cube_consumer": <JSON value>}, ...
  ]
}

The supplied `cube` value is the proposed hiddenToCube(h). For every row with
`next_id`, this script checks P(hiddenNext h) == cubeStep(P(h)); every projected
state must satisfy the concrete cube GraphLaw; consumer values must agree.
This validates a supplied projection/trajectory receipt. It does not learn P.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

P = 3
SIDE = 3


def fi(x: int, y: int) -> int:
    return SIDE * x + y


def add_face(a, b):
    return tuple((x + y) % P for x, y in zip(a, b))


def sub_face(a, b):
    return tuple((x - y) % P for x, y in zip(a, b))


def bop(f):
    return tuple(
        (f[fi((x + 1) % 3, y)] + f[fi(x, (y + 1) % 3)]) % P
        for x in range(3)
        for y in range(3)
    )


def bop2(f):
    return bop(bop(f))


def split_cube(c):
    return tuple(c[:9]), tuple(c[9:18]), tuple(c[18:27])


def join_cube(a, b, c):
    return tuple(a) + tuple(b) + tuple(c)


def cube_step(c):
    u0, u1, u2 = split_cube(c)
    return join_cube(
        add_face(bop(u0), u1),
        add_face(bop(u1), u2),
        add_face(bop(u2), u0),
    )


def graph_law(c):
    y0, y1, y2 = split_cube(c)
    return tuple(y2) == sub_face(bop(y1), bop2(y0))


def validate_cube(c):
    return (
        isinstance(c, list)
        and len(c) == 27
        and all(isinstance(x, int) and 0 <= x < 3 for x in c)
    )


def evaluate(payload):
    rows = payload["rows"]
    by_id = {row["id"]: row for row in rows}
    if len(by_id) != len(rows):
        raise ValueError("duplicate row id")
    for row in rows:
        if not validate_cube(row["cube"]):
            raise ValueError(f"invalid cube for {row['id']}")

    reachable = [row["id"] for row in rows if graph_law(tuple(row["cube"]))]

    transition_checks = []
    missing_next_rows = []
    for row in rows:
        next_id = row.get("next_id")
        if next_id is None:
            continue
        if next_id not in by_id:
            missing_next_rows.append((row["id"], next_id))
            continue
        transition_checks.append(
            (
                row["id"],
                cube_step(tuple(row["cube"])) == tuple(by_id[next_id]["cube"]),
            )
        )

    consumer_checks = [
        (row["id"], row.get("hidden_consumer") == row.get("cube_consumer"))
        for row in rows
    ]
    heldout = [row for row in rows if row.get("split") == "heldout"]

    return {
        "row_count": len(rows),
        "heldout_count": len(heldout),
        "all_projected_states_reachable": len(reachable) == len(rows),
        "reachable_row_ids": reachable,
        "transition_checks": transition_checks,
        "all_declared_transitions_intertwine": (
            bool(transition_checks)
            and all(ok for _row_id, ok in transition_checks)
            and not missing_next_rows
        ),
        "missing_next_rows": missing_next_rows,
        "consumer_checks": consumer_checks,
        "all_consumers_factor": all(ok for _row_id, ok in consumer_checks),
        "heldout_consumer_payment_present": (
            bool(heldout)
            and all(
                row.get("hidden_consumer") == row.get("cube_consumer")
                for row in heldout
            )
        ),
        "boundary": (
            "validates supplied hidden->cube projection rows; does not learn the projection "
            "and does not manufacture missing model trajectories"
        ),
    }


def self_test_payload():
    # Reachable fixed zero state tests the receipt plumbing only; it is not
    # empirical LILA/model evidence.
    zero = [0] * 27
    return {
        "rows": [
            {
                "id": "t0",
                "next_id": "t1",
                "split": "train",
                "cube": zero,
                "hidden_consumer": 0,
                "cube_consumer": 0,
            },
            {
                "id": "t1",
                "next_id": "t2",
                "split": "heldout",
                "cube": zero,
                "hidden_consumer": 1,
                "cube_consumer": 1,
            },
            {
                "id": "t2",
                "split": "heldout",
                "cube": zero,
                "hidden_consumer": 2,
                "cube_consumer": 2,
            },
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        payload = self_test_payload()
    elif args.input:
        payload = json.loads(args.input.read_text())
    else:
        parser.error("--input or --self-test required")

    result = evaluate(payload)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")

    if args.self_test:
        assert result["all_projected_states_reachable"]
        assert result["all_declared_transitions_intertwine"]
        assert result["all_consumers_factor"]
        assert result["heldout_consumer_payment_present"]


if __name__ == "__main__":
    main()
