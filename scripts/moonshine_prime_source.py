#!/usr/bin/env python3
"""Build a moonshine-native source-family manifest from repo modules."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path


MOONSHINE_DIR = Path("DASHI/Physics/Moonshine")


@dataclass(frozen=True)
class SourceFamily:
    module_path: str
    family_kind: str
    family_label: str
    realization: str
    trace_like: bool


def classify(path: Path) -> SourceFamily | None:
    name = path.name
    stem = path.stem
    if not name.endswith(".agda"):
        return None

    if "FiniteTwined" in stem or "TwinedTrace" in stem:
        kind = "finite_twined_trace"
        trace_like = True
    elif "FiniteGradedShellSeries" in stem or "Graded" in stem:
        kind = "finite_graded_series"
        trace_like = True
    elif "TwinedWave" in stem or "TraceFamilySummary" in stem:
        kind = "twined_wave_summary"
        trace_like = True
    elif "Comparison" in stem or "Report" in stem or "Summary" in stem:
        kind = "comparison_or_summary"
        trace_like = False
    else:
        return None

    if "RootSystemB4" in stem or "B4" in stem:
        realization = "root_system_b4"
    elif "Shift" in stem:
        realization = "shift"
    else:
        realization = "mixed_or_unspecified"

    return SourceFamily(
        module_path=str(path),
        family_kind=kind,
        family_label=stem,
        realization=realization,
        trace_like=trace_like,
    )


def build_manifest() -> dict[str, object]:
    families = []
    for path in sorted(MOONSHINE_DIR.glob("*.agda")):
        classified = classify(path)
        if classified is not None:
            families.append(classified)

    return {
        "manifest_kind": "moonshine_prime_source_families",
        "source_root": str(MOONSHINE_DIR),
        "family_count": len(families),
        "families": [asdict(f) for f in families],
        "promotion_note": (
            "Only trace-like moonshine-native families should feed the moonshine-prime object lane; "
            "photonuclear prototype states are out of scope."
        ),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", help="Optional path for manifest JSON")
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    manifest = build_manifest()
    text = json.dumps(manifest, indent=2 if args.pretty else None, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + ("\n" if args.pretty else ""))
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
