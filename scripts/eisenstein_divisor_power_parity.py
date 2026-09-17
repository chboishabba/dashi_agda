"""Independent finite parity probe for the Agda divisor-power kernel.

This script deliberately does not define Agda semantics or modular-form authority.
It recomputes sigma_k by Python divisor enumeration and compares finite prefixes
against the public OEIS sequence coordinates A001158 (sigma_3) and A001160
(sigma_5).
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


def sigma_power(n: int, exponent: int) -> int:
    if n < 1:
        return 0
    return sum(d ** exponent for d in range(1, n + 1) if n % d == 0)


def prefix(exponent: int, length: int) -> list[int]:
    return [sigma_power(n, exponent) for n in range(1, length + 1)]


def parity_report() -> dict[str, object]:
    sigma3_prefix = prefix(3, len(OEIS_A001158_PREFIX))
    sigma5_prefix = prefix(5, len(OEIS_A001160_PREFIX))
    return {
        "sigma3_oeis_id": "A001158",
        "sigma5_oeis_id": "A001160",
        "sigma3_prefix": sigma3_prefix,
        "sigma5_prefix": sigma5_prefix,
        "sigma3_matches_oeis_prefix": sigma3_prefix == OEIS_A001158_PREFIX,
        "sigma5_matches_oeis_prefix": sigma5_prefix == OEIS_A001160_PREFIX,
        "oeis_defines_kernel": False,
        "finite_prefix_proves_infinite_series": False,
        "finite_prefix_proves_modularity": False,
    }


if __name__ == "__main__":
    report = parity_report()
    print(json.dumps(report, sort_keys=True))
    if not (
        report["sigma3_matches_oeis_prefix"]
        and report["sigma5_matches_oeis_prefix"]
    ):
        raise SystemExit(1)
