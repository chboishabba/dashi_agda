#!/usr/bin/env python3
"""Normalize the observed moonshine-prime object into a stable quotient form."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

SSP_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]


@dataclass(frozen=True)
class EigenProfile:
    earth: int
    spoke: int
    hub: int

    @property
    def numerator(self) -> dict[str, int]:
        return {"earth": self.earth, "spoke": self.spoke, "hub": self.hub}

    @property
    def denominator_from_profile(self) -> int:
        return self.earth + self.spoke + self.hub


@dataclass(frozen=True)
class MoonshinePrimeState:
    carrier: tuple[int, ...]
    signature: dict[int, bool]
    eigen_profile: EigenProfile
    basin_label: str
    factor_vector: dict[int, int]
    mdl_level: int


@dataclass(frozen=True)
class MoonshinePrimeObservable:
    signature: dict[int, bool]
    eigen_numerator: dict[str, int]
    eigen_denominator: int
    mdl_denominator: int
    basin_label: str
    factor_support: tuple[int, ...]
    factor_support_weight: int
    factor_vector: dict[int, int]


def _parse_prime_dict(raw: Any, *, value_name: str, cast: type) -> dict[int, Any]:
    if isinstance(raw, dict):
        parsed = {int(k): cast(v) for k, v in raw.items()}
    elif isinstance(raw, list):
        if len(raw) != len(SSP_PRIMES):
            raise ValueError(
                f"{value_name} list must have length {len(SSP_PRIMES)}, got {len(raw)}"
            )
        parsed = {p: cast(v) for p, v in zip(SSP_PRIMES, raw)}
    else:
        raise ValueError(f"{value_name} must be a dict or list")

    missing = [p for p in SSP_PRIMES if p not in parsed]
    extra = sorted(set(parsed) - set(SSP_PRIMES))
    if missing or extra:
        raise ValueError(
            f"{value_name} keys must match SSP primes; missing={missing}, extra={extra}"
        )
    return {p: parsed[p] for p in SSP_PRIMES}


def parse_state(payload: dict[str, Any]) -> MoonshinePrimeState:
    try:
        carrier_raw = payload["carrier"]
        signature_raw = payload["signature"]
        eigen_raw = payload["eigenProfile"]
        basin_label = str(payload["basinLabel"])
        factor_raw = payload["factorVector"]
        mdl_level = int(payload["mdlLevel"])
    except KeyError as exc:
        raise ValueError(f"missing required field: {exc.args[0]}") from exc

    if not isinstance(carrier_raw, list):
        raise ValueError("carrier must be a list of integers")

    carrier = tuple(int(v) for v in carrier_raw)
    signature = _parse_prime_dict(signature_raw, value_name="signature", cast=bool)
    factor_vector = _parse_prime_dict(factor_raw, value_name="factorVector", cast=int)

    eigen_profile = EigenProfile(
        earth=int(eigen_raw["earth"]),
        spoke=int(eigen_raw["spoke"]),
        hub=int(eigen_raw["hub"]),
    )

    return MoonshinePrimeState(
        carrier=carrier,
        signature=signature,
        eigen_profile=eigen_profile,
        basin_label=basin_label,
        factor_vector=factor_vector,
        mdl_level=mdl_level,
    )


def observe(state: MoonshinePrimeState) -> MoonshinePrimeObservable:
    factor_support = tuple(
        p for p in SSP_PRIMES if state.factor_vector[p] > 0 or state.signature[p]
    )
    factor_support_weight = sum(state.factor_vector[p] for p in factor_support)
    denominator = state.eigen_profile.denominator_from_profile

    return MoonshinePrimeObservable(
        signature=state.signature,
        eigen_numerator=state.eigen_profile.numerator,
        eigen_denominator=denominator,
        mdl_denominator=state.mdl_level,
        basin_label=state.basin_label,
        factor_support=factor_support,
        factor_support_weight=factor_support_weight,
        factor_vector=state.factor_vector,
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="Path to a MoonshinePrimeState JSON file")
    parser.add_argument(
        "--output",
        help="Optional path for the normalized MoonshinePrimeObservable JSON",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print JSON output",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    payload = json.loads(Path(args.input).read_text())
    state = parse_state(payload)
    observable = observe(state)
    json_text = json.dumps(asdict(observable), indent=2 if args.pretty else None, sort_keys=True)

    if args.output:
        Path(args.output).write_text(json_text + ("\n" if args.pretty else ""))
    else:
        print(json_text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
