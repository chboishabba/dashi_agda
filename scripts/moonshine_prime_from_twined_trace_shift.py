#!/usr/bin/env python3
"""Lift the explicit orientation-prime hook and auxiliary report fields."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from moonshine_prime_object import SSP_PRIMES


SOURCE_PATH = Path("DASHI/Physics/Moonshine/FiniteTwinedShellTraceShift.agda")
DETAILED_REPORT_PATH = Path("DASHI/Physics/Moonshine/FiniteTwinedTraceDetailedReport.agda")
FAMILY_SUMMARY_PATH = Path("DASHI/Physics/Moonshine/MoonshineTraceFamilySummary.agda")
PROTOTYPE_BUNDLE_PATH = Path("DASHI/Physics/Moonshine/MoonshinePrototypeComparisonBundle.agda")
SHIFT_LIBRARY_PATH = Path("DASHI/Physics/Moonshine/FiniteTwinerLibraryShift.agda")
CONSTRUCTOR_PATTERNS = {
    "identity": re.compile(
        r"shiftIdentityTwinedTrace\s*:.*?identityTwinedTrace\s*\(\s*just\s+(\d+)\s*\)",
        re.S,
    ),
    "nontrivial": re.compile(
        r"shiftNontrivialTwinedTrace\s*:.*?twinedTraceFromAction.*?\(\s*just\s+(\d+)\s*\)",
        re.S,
    ),
}
SHIFT_LABEL_PATTERN = re.compile(r'label\s*=\s*"([^"]+)"')
DETAIL_SLOT_PATTERN = re.compile(
    r"^\s+([A-Za-z0-9]+Verdict)\s*:\s*LabeledTwinedVerdict", re.M
)
EXTRA_VERDICT_PATTERN = re.compile(
    r"mkVerdict\s+TLS\.([A-Za-z0-9]+)\s+TLB4\.([A-Za-z0-9]+)"
)
EXTRA_VERDICTS_BLOCK_PATTERN = re.compile(
    r"extraVerdicts\s*=\s*(.*?)\n\s*\}", re.S
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--constructor",
        choices=sorted(CONSTRUCTOR_PATTERNS),
        default="identity",
        help="Which exported shift trace constructor to anchor provenance on",
    )
    parser.add_argument("--output", help="Optional path for MoonshinePrimeState JSON")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def extract_orientation_prime(text: str, constructor: str) -> int:
    match = CONSTRUCTOR_PATTERNS[constructor].search(text)
    if match is None:
        raise ValueError(
            f"could not extract orientation prime for constructor '{constructor}'"
        )
    return int(match.group(1))


def extract_shift_labels(text: str) -> list[str]:
    return SHIFT_LABEL_PATTERN.findall(text)


def camel_to_kebabish(name: str) -> str:
    if not name:
        return name
    return name[0].lower() + name[1:]


def extract_extra_verdict_pairs(text: str) -> list[tuple[str, str]]:
    block_match = EXTRA_VERDICTS_BLOCK_PATTERN.search(text)
    if block_match is None:
        return []
    return EXTRA_VERDICT_PATTERN.findall(block_match.group(1))


def build_trace_report() -> dict[str, Any]:
    detailed_text = DETAILED_REPORT_PATH.read_text()
    shift_library_text = SHIFT_LIBRARY_PATH.read_text()

    explicit_slots = DETAIL_SLOT_PATTERN.findall(detailed_text)
    extra_pairs = extract_extra_verdict_pairs(detailed_text)
    shift_labels = extract_shift_labels(shift_library_text)

    extra_shift_labels = [
        camel_to_kebabish(shift_name.replace("shiftTwiner", ""))
        for shift_name, _ in extra_pairs
    ]

    return {
        "summary_sources": {
            "detailed_report": str(DETAILED_REPORT_PATH),
            "family_summary": str(FAMILY_SUMMARY_PATH),
            "prototype_bundle": str(PROTOTYPE_BUNDLE_PATH),
            "shift_library": str(SHIFT_LIBRARY_PATH),
        },
        "explicit_verdict_slots": explicit_slots,
        "explicit_verdict_count": len(explicit_slots) + len(extra_pairs),
        "extra_verdict_count": len(extra_pairs),
        "extra_shift_labels": extra_shift_labels,
        "shift_twiner_labels": shift_labels,
        "compared_twiner_count": len(extra_pairs),
    }


def build_state(*, orientation_prime: int, constructor: str) -> dict[str, Any]:
    if orientation_prime not in SSP_PRIMES:
        raise ValueError(
            f"orientation prime {orientation_prime} is outside the SSP prime support"
        )

    signature = {str(p): p == orientation_prime for p in SSP_PRIMES}
    factor_vector = {str(p): 1 if p == orientation_prime else 0 for p in SSP_PRIMES}
    trace_report = build_trace_report()
    factor_support = [int(p) for p, flag in signature.items() if flag]
    eigen_profile = {"earth": 0, "spoke": 0, "hub": 1}
    eigen_total = sum(eigen_profile.values())
    eigen_ratio = eigen_profile["hub"] / (eigen_total or 1)
    normalized_observable = {
        "factorSupport": factor_support,
        "supportWeight": len(factor_support),
        "signatureDensity": sum(signature.values()),
        "eigenNumerator": eigen_profile["hub"],
        "eigenDenominator": eigen_total or 1,
        "eigenRatio": eigen_ratio,
        "mdlLevel": orientation_prime,
        "verdictCount": trace_report["explicit_verdict_count"],
        "comparedTwinerCount": trace_report["compared_twiner_count"],
        "reportSummary": {
            "explicitSlots": trace_report["explicit_verdict_slots"],
            "extraShiftLabels": trace_report["extra_shift_labels"],
        },
    }

    return {
        "carrier": [orientation_prime],
        "signature": signature,
        "eigenProfile": {"earth": 0, "spoke": 0, "hub": 1},
        "basinLabel": "orientation_prime_only",
        "factorVector": factor_vector,
        "mdlLevel": orientation_prime,
        "provenance": {
            "adapter": "moonshine_prime_from_twined_trace_shift",
            "source_module": str(SOURCE_PATH),
            "source_constructor": constructor,
            "source_boundary": "orientation_prime_only",
            "orientation_prime": orientation_prime,
        },
        "traceReport": trace_report,
        "normalizedObservable": normalized_observable,
    }


def main() -> int:
    args = parse_args()
    text = SOURCE_PATH.read_text()
    orientation_prime = extract_orientation_prime(text, args.constructor)
    state = build_state(
        orientation_prime=orientation_prime,
        constructor=args.constructor,
    )
    json_text = json.dumps(state, indent=2 if args.pretty else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(json_text + ("\n" if args.pretty else ""))
    else:
        print(json_text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
