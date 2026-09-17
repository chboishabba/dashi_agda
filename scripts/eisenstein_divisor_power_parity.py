"""Independent finite parity probe for the Agda divisor-power/Eisenstein lane.

This script deliberately does not define Agda semantics or modular-form authority.
It recomputes sigma_k by Python divisor enumeration, derives the normalized E4/E6
coefficient prefixes from those values, and compares finite prefixes against the
public OEIS coordinates A001158/A001160 and A004009/A013973.
"""

from __future__ import annotations

import json

OEIS_A001158_PREFIX = [
    1, 9, 28, 73, 126, 252, 344, 585, 757, 1134,
    1332, 2044, 2198, 3096, 3528,
]

OEIS_A001160_PREFIX = [
    1, 33, 244, 1057, 3126, 8052, 16808, 33825, 59293, 103158,
    161052, 257908, 371294, 554664, 762744,
]

OEIS_A004009_PREFIX = [
    1, 240, 2160, 6720, 17520, 30240, 60480,
    82560, 140400, 181680, 272160,
]

OEIS_A013973_PREFIX = [
    1, -504, -16632, -122976, -532728, -1575504, -4058208,
    -8471232, -17047800, -29883672, -51991632,
]


def sigma_power(n: int, exponent: int) -> int:
    if n < 1:
        return 0
    return sum(d ** exponent for d in range(1, n + 1) if n % d == 0)


def prefix(exponent: int, length: int) -> list[int]:
    return [sigma_power(n, exponent) for n in range(1, length + 1)]


def e4_prefix(length: int) -> list[int]:
    if length < 1:
        return []
    return [1] + [240 * sigma_power(n, 3) for n in range(1, length)]


def e6_prefix(length: int) -> list[int]:
    if length < 1:
        return []
    return [1] + [-504 * sigma_power(n, 5) for n in range(1, length)]


def parity_report() -> dict[str, object]:
    sigma3_prefix = prefix(3, len(OEIS_A001158_PREFIX))
    sigma5_prefix = prefix(5, len(OEIS_A001160_PREFIX))
    e4 = e4_prefix(len(OEIS_A004009_PREFIX))
    e6 = e6_prefix(len(OEIS_A013973_PREFIX))
    return {
        "sigma3_oeis_id": "A001158",
        "sigma5_oeis_id": "A001160",
        "e4_oeis_id": "A004009",
        "e6_oeis_id": "A013973",
        "sigma3_prefix": sigma3_prefix,
        "sigma5_prefix": sigma5_prefix,
        "e4_prefix": e4,
        "e6_prefix": e6,
        "sigma3_matches_oeis_prefix": sigma3_prefix == OEIS_A001158_PREFIX,
        "sigma5_matches_oeis_prefix": sigma5_prefix == OEIS_A001160_PREFIX,
        "e4_matches_oeis_prefix": e4 == OEIS_A004009_PREFIX,
        "e6_matches_oeis_prefix": e6 == OEIS_A013973_PREFIX,
        "oeis_defines_kernel": False,
        "oeis_defines_eisenstein_coefficients": False,
        "finite_prefix_proves_infinite_series": False,
        "finite_prefix_proves_modularity": False,
    }


if __name__ == "__main__":
    report = parity_report()
    print(json.dumps(report, sort_keys=True))
    if not all(
        report[key]
        for key in (
            "sigma3_matches_oeis_prefix",
            "sigma5_matches_oeis_prefix",
            "e4_matches_oeis_prefix",
            "e6_matches_oeis_prefix",
        )
    ):
        raise SystemExit(1)
