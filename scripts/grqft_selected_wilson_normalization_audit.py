#!/usr/bin/env python3
"""Exact-rational multi-probe Wilson/CMP119 source-normalization audit.

Checks supplied SU(2) plaquette traces and the full selected exponent after
the E/R/B/vacuum sectors are subtracted. It DOES NOT establish that these
supplied traces and sectors come from the published CMP119 source.
References: Wilson (1974), DOI 10.1103/PhysRevD.10.2445;
Balaban CMP109 (1987), DOI 10.1007/BF01215223;
Balaban CMP119 (1988), DOI 10.1007/BF01217741.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys

SECTORS = ("E", "R", "B", "vacuum")


def q(value: object) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError(f"Expected exact rational string/int, got {value!r}")
    return Fraction(value)


def required_text(data: dict, key: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"Missing or empty {key}")
    return value


def audit(data: dict) -> dict:
    provenance = data.get("provenance")
    if not isinstance(provenance, dict):
        raise ValueError("Missing provenance")
    for key in ("source_identifier", "source_revision", "source_locator",
                "action_identifier", "coupling_identifier", "cutoff",
                "plaquette_basis", "trace_convention", "coefficient_origin"):
        required_text(provenance, key)
    if provenance["plaquette_basis"] != "Wplus=sum(1-ReTrU/2)":
        raise ValueError("Unrecognized Wilson plaquette basis")
    convention = data.get("bare_coefficient_convention")
    if convention not in ("unit_inverse_square", "standard_SU2_four_inverse_square"):
        raise ValueError("Specify exact SU2 Wilson coefficient convention")
    factor = Fraction(1 if convention == "unit_inverse_square" else 4)
    g2, u = q(data["g_squared"]), q(data["inverse_g_squared"])
    if g2 <= 0 or g2 * u != 1:
        raise ValueError("Selected g_squared must be positive with exact inverse product one")
    if data.get("selected_exponent_sign") != "log_density=-action":
        raise ValueError("Unsupported action/exponent sign convention")
    configs = data.get("configurations")
    if not isinstance(configs, list) or len(configs) < 2:
        raise ValueError("At least two distinct finite SU2 probes required")
    expected = -factor * u
    seen, results, inferred = set(), [], []
    for item in configs:
        if not isinstance(item, dict):
            raise ValueError("Probe must be an object")
        name = required_text(item, "configuration_id")
        if name in seen:
            raise ValueError("Repeated configuration identity")
        seen.add(name)
        traces = item.get("plaquette_normalized_real_traces")
        if not isinstance(traces, list) or not traces:
            raise ValueError("Need literal normalized SU2 traces")
        traces = [q(t) for t in traces]
        if any(t < -1 or t > 1 for t in traces):
            raise ValueError("Normalized SU2 trace outside [-1,1]")
        w = sum((1 - t for t in traces), Fraction())
        sectors = item.get("exponent_nonwilson_sectors")
        if not isinstance(sectors, dict) or set(sectors) != set(SECTORS):
            raise ValueError("Expected exact E/R/B/vacuum exponent sectors")
        correction = sum((q(sectors[s]) for s in SECTORS), Fraction())
        selected = q(item["selected_total_log_density_exponent"])
        wilson = selected - correction
        if w == 0 and wilson:
            raise ValueError(f"Zero Wilson-cost {name} carries nonzero Wilson exponent")
        ratio = wilson / w if w else None
        if ratio is not None:
            inferred.append(ratio)
        results.append({
            "configuration_id": name, "Wplus": str(w),
            "nonwilson_exponent_sum": str(correction),
            "source_wilson_exponent": str(wilson),
            "inferred_coefficient": str(ratio) if ratio is not None else None,
            "expected_source_wilson_exponent": str(expected * w),
            "normalized_probe_matches_expected": wilson == expected * w,
        })
    if len(inferred) < 2:
        raise ValueError("Two nonzero Wilson probes required")
    if len(set(inferred)) != 1:
        raise ValueError("CMP119 Wilson coefficients disagree across probes")
    if inferred[0] != expected:
        raise ValueError(f"Selected Wilson coefficient mismatch: {inferred[0]} vs {expected}")
    return {
        "status": "finite_exact_rational_multi_probe_consistency_only",
        "published_cmp119_source_identification_proved": False,
        "physical_SU2_matrix_rows_proved": False,
        "nonwilson_sector_derivations_proved": False,
        "renormalized_continuum_proved": False,
        "provenance": provenance, "coefficient_convention": convention,
        "g_squared": str(g2), "inverse_g_squared": str(u),
        "expected_wilson_exponent_coefficient": str(expected),
        "recovered_multi_probe_coefficient": str(inferred[0]),
        "probe_count": len(results), "nonzero_probe_count": len(inferred),
        "all_probe_exponents_match": True, "rows": results,
        "warning": "Supply independently validated selected action, trace matrices, sector derivations, cutoff and provenance; a rational receipt alone is not a CMP119 physical proof."
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    try:
        source_bytes = args.source.read_bytes()
        result = audit(json.loads(source_bytes))
        result["input_sha256"] = hashlib.sha256(source_bytes).hexdigest()
        output = json.dumps(result, sort_keys=True, indent=2) + "\n"
        if args.out:
            args.out.write_text(output)
        else:
            print(output, end="")
        return 0
    except (ValueError, TypeError, KeyError, OSError, ZeroDivisionError) as error:
        print(f"FAIL-CLOSED: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
