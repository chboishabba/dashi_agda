#!/usr/bin/env python3
"""Quick diagnostic for the lightweight null-transport to modulo-null consumer."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


DEFAULT_OUTPUT = Path("outputs/unification_null_transport_modulo_null_consumer_harness.json")


@dataclass(frozen=True)
class Result:
    quotient_transport_error: float
    modulo_null_additivity_error: float
    four_point_input_error: float
    promotion: bool
    checks: dict[str, bool]


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--json-output", type=Path, default=DEFAULT_OUTPUT)
    return parser.parse_args(argv)


def quotient(x: list[float]) -> list[float]:
    return x[:2]


def gluing(x: list[float]) -> list[float]:
    q = quotient(x)
    return [q[0] + 2.0 * q[1], -q[0] + q[1], 0.0, 0.0]


def build_result() -> Result:
    x = [1.0, 2.0, 0.1, -0.1]
    y = [-3.0, 1.5, 0.3, 0.2]
    x_equiv = [1.0, 2.0, 0.4, 0.7]
    q_transport = max(abs(a - b) for a, b in zip(quotient(x), quotient(x_equiv)))
    add_error = max(abs(a - b) for a, b in zip(gluing([x[i] + y[i] for i in range(4)]), [gluing(x)[i] + gluing(y)[i] for i in range(4)]))
    cross = [gluing([x[i] + y[i] for i in range(4)])[i] - gluing(x)[i] - gluing(y)[i] for i in range(4)]
    four_point_input_error = max(abs(v) for v in quotient(cross))
    checks = {
        "quotient_transport": q_transport == 0.0,
        "modulo_null_additivity": add_error == 0.0,
        "cross_term_quotient_zero": four_point_input_error == 0.0,
    }
    return Result(q_transport, add_error, four_point_input_error, False, checks)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    result = build_result()
    payload = asdict(result)
    args.json_output.parent.mkdir(parents=True, exist_ok=True)
    args.json_output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        print(f"quotient_transport_error={result.quotient_transport_error}")
        print(f"promotion={result.promotion}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
