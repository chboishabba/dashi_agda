#!/usr/bin/env python3
"""Search for a separating pair under the full profileSummaryFamily invariant.

This script is intentionally thin:
- it fixes the current generator taxonomy used by the Agda layer,
- it canonicalizes a Vec15-style family of DefectOrbitSummary records,
- it reports the first separating pair if one exists, or
- emits a collapse certificate over the searched generator set.

The actual summary computation is injected through a Python module/function so
the mirror can be wired to whatever local search or adapter layer is available.
"""

from __future__ import annotations

import argparse
import importlib
import json
import sys
from dataclasses import asdict, is_dataclass
from itertools import combinations
from typing import Any, Callable

DEFAULT_GENERATORS = (
    "explicitWidth1",
    "explicitWidth2",
    "explicitWidth3",
    "balancedCycle",
    "denseComposed",
    "balancedComposed",
    "anchoredTrajectory",
    "supportCascade",
    "fullSupportCascade",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--module",
        default="profile_summary_adapter",
        help="Python module providing the profile-summary family function",
    )
    parser.add_argument(
        "--function",
        default="profile_summary_family",
        help="Function name in --module that accepts one generator name",
    )
    parser.add_argument(
        "--generators",
        nargs="*",
        default=list(DEFAULT_GENERATORS),
        help="Generator names to compare; defaults to the current taxonomy",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON output",
    )
    return parser.parse_args()


def _summary_as_dict(summary: Any) -> dict[str, Any]:
    if isinstance(summary, dict):
        return summary
    if is_dataclass(summary):
        return asdict(summary)
    if hasattr(summary, "__dict__"):
        return dict(vars(summary))
    raise TypeError(f"unsupported summary payload: {type(summary)!r}")


def canonical_summary_family(vec15: list[Any]) -> tuple[tuple[int, int, int, int, int, int], ...]:
    out: list[tuple[int, int, int, int, int, int]] = []
    for summary in vec15:
        data = _summary_as_dict(summary)
        out.append(
            (
                int(data["forcedStableCount"]),
                int(data["motifChangeCount"]),
                int(data["totalDrift"]),
                int(data["repatterningCount"]),
                int(data["contractiveCount"]),
                int(data["expansiveCount"]),
            )
        )
    return tuple(out)


def load_profile_summary_family(module_name: str, function_name: str) -> Callable[[str], list[Any]]:
    module = importlib.import_module(module_name)
    fn = getattr(module, function_name, None)
    if fn is None or not callable(fn):
        raise AttributeError(f"{module_name}.{function_name} is not callable")
    return fn


def find_separator(
    generator_names: list[str],
    profile_summary_family_fn: Callable[[str], list[Any]],
) -> dict[str, Any]:
    encoded: dict[str, tuple[tuple[int, int, int, int, int, int], ...]] = {}

    for name in generator_names:
        encoded[name] = canonical_summary_family(profile_summary_family_fn(name))

    for left, right in combinations(generator_names, 2):
        if encoded[left] != encoded[right]:
            return {
                "separates": True,
                "left": left,
                "right": right,
                "left_summary": encoded[left],
                "right_summary": encoded[right],
            }

    return {
        "separates": False,
        "collapse_classes": encoded,
    }


def main() -> None:
    args = parse_args()
    try:
        profile_summary_family_fn = load_profile_summary_family(args.module, args.function)
        result = find_separator(args.generators, profile_summary_family_fn)
    except (ImportError, AttributeError, NotImplementedError, TypeError, KeyError) as exc:
        error = {
            "separates": None,
            "error": str(exc),
            "module": args.module,
            "function": args.function,
            "generators": args.generators,
        }
        print(json.dumps(error, indent=2 if args.pretty else None, sort_keys=True))
        raise SystemExit(2)
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
