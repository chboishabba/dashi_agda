#!/usr/bin/env python3
"""Solar weak-field GR baseline diagnostic.

This script emits concrete external-GR baseline predictions for standard solar
weak-field tests.  It is a calibration target surface only: it does not promote
any DASHI carrier-internal gravity claim.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_JSON_OUTPUT = Path("scripts/data/outputs/solar_weak_field_gr_baseline_diagnostic.json")
DEFAULT_CSV_OUTPUT = Path("scripts/data/outputs/solar_weak_field_gr_baseline_diagnostic.csv")

PROMOTION_STATUS = "NO_PROMOTION"

# SI baseline constants used for this diagnostic.
SPEED_OF_LIGHT_M_PER_S = 299_792_458.0
SOLAR_GM_M3_PER_S2 = 1.327_124_400_18e20
SOLAR_RADIUS_M = 6.957e8
ASTRONOMICAL_UNIT_M = 149_597_870_700.0
JULIAN_CENTURY_DAYS = 36_525.0
SECONDS_PER_DAY = 86_400.0
MERCURY_SEMIMAJOR_AXIS_AU = 0.387_098_93
MERCURY_ECCENTRICITY = 0.205_630_69
EARTH_ORBIT_RADIUS_AU = 1.0

RAD_TO_ARCSEC = 180.0 * 3_600.0 / math.pi


@dataclass(frozen=True)
class DiagnosticRecord:
    test_name: str
    quantity: str
    value: float
    unit: str
    formula: str
    context: str

    def as_row(self) -> dict[str, Any]:
        return {
            "test_name": self.test_name,
            "quantity": self.quantity,
            "value": self.value,
            "unit": self.unit,
            "formula": self.formula,
            "context": self.context,
            "promotion_status": PROMOTION_STATUS,
            "carrier_internal": False,
            "external_gr_baseline": True,
            "calibration_required": True,
        }


def mercury_perihelion_advance() -> list[DiagnosticRecord]:
    a_m = MERCURY_SEMIMAJOR_AXIS_AU * ASTRONOMICAL_UNIT_M
    e = MERCURY_ECCENTRICITY
    advance_rad_per_orbit = (
        6.0 * math.pi * SOLAR_GM_M3_PER_S2 / (a_m * (1.0 - e * e) * SPEED_OF_LIGHT_M_PER_S**2)
    )
    orbital_period_seconds = 2.0 * math.pi * math.sqrt(a_m**3 / SOLAR_GM_M3_PER_S2)
    orbits_per_century = JULIAN_CENTURY_DAYS * SECONDS_PER_DAY / orbital_period_seconds
    advance_arcsec_per_century = advance_rad_per_orbit * RAD_TO_ARCSEC * orbits_per_century

    return [
        DiagnosticRecord(
            test_name="mercury_perihelion_advance",
            quantity="advance_per_orbit",
            value=advance_rad_per_orbit,
            unit="rad/orbit",
            formula="6*pi*GM_sun/(a*(1-e^2)*c^2)",
            context="Mercury osculating a=0.38709893 AU, e=0.20563069",
        ),
        DiagnosticRecord(
            test_name="mercury_perihelion_advance",
            quantity="advance_per_century",
            value=advance_arcsec_per_century,
            unit="arcsec/Julian_century",
            formula="advance_per_orbit*rad_to_arcsec*century/orbital_period",
            context="GR excess perihelion advance scale for Mercury",
        ),
    ]


def solar_light_deflection() -> DiagnosticRecord:
    deflection_rad = 4.0 * SOLAR_GM_M3_PER_S2 / (SPEED_OF_LIGHT_M_PER_S**2 * SOLAR_RADIUS_M)
    return DiagnosticRecord(
        test_name="solar_light_deflection_limb",
        quantity="deflection_angle",
        value=deflection_rad * RAD_TO_ARCSEC,
        unit="arcsec",
        formula="4*GM_sun/(c^2*R_sun)",
        context="grazing ray at one solar radius impact parameter",
    )


def shapiro_delay_scale(receiver_orbit_radius_au: float) -> list[DiagnosticRecord]:
    earth_radius_m = EARTH_ORBIT_RADIUS_AU * ASTRONOMICAL_UNIT_M
    receiver_radius_m = receiver_orbit_radius_au * ASTRONOMICAL_UNIT_M
    gravitational_time_scale_s = SOLAR_GM_M3_PER_S2 / SPEED_OF_LIGHT_M_PER_S**3
    one_way_delay_s = (
        2.0
        * gravitational_time_scale_s
        * math.log(4.0 * earth_radius_m * receiver_radius_m / SOLAR_RADIUS_M**2)
    )
    return [
        DiagnosticRecord(
            test_name="solar_shapiro_delay_scale",
            quantity="solar_gravitational_time_unit",
            value=gravitational_time_scale_s * 1.0e6,
            unit="microsecond",
            formula="GM_sun/c^3",
            context="solar mass time scale",
        ),
        DiagnosticRecord(
            test_name="solar_shapiro_delay_scale",
            quantity="grazing_one_way_delay",
            value=one_way_delay_s * 1.0e6,
            unit="microsecond",
            formula="(2*GM_sun/c^3)*ln(4*r_earth*r_receiver/b^2)",
            context=(
                "superior-conjunction scale with r_earth=1 AU, "
                f"r_receiver={receiver_orbit_radius_au:g} AU, b=R_sun"
            ),
        ),
    ]


def gravitational_redshift_scale() -> list[DiagnosticRecord]:
    z = SOLAR_GM_M3_PER_S2 / (SOLAR_RADIUS_M * SPEED_OF_LIGHT_M_PER_S**2)
    return [
        DiagnosticRecord(
            test_name="solar_gravitational_redshift_scale",
            quantity="redshift_z",
            value=z,
            unit="dimensionless",
            formula="Delta_nu/nu ~= GM_sun/(R_sun*c^2)",
            context="solar photosphere to infinity weak-field scale",
        ),
        DiagnosticRecord(
            test_name="solar_gravitational_redshift_scale",
            quantity="velocity_equivalent",
            value=z * SPEED_OF_LIGHT_M_PER_S,
            unit="m/s",
            formula="c*z",
            context="velocity-equivalent solar gravitational redshift scale",
        ),
    ]


def build_records(receiver_orbit_radius_au: float) -> list[dict[str, Any]]:
    records: list[DiagnosticRecord] = []
    records.extend(mercury_perihelion_advance())
    records.append(solar_light_deflection())
    records.extend(shapiro_delay_scale(receiver_orbit_radius_au))
    records.extend(gravitational_redshift_scale())
    return [record.as_row() for record in records]


def build_payload(records: list[dict[str, Any]], receiver_orbit_radius_au: float) -> dict[str, Any]:
    return {
        "artifact_schema": "dashi-solar-weak-field-gr-baseline-diagnostic-v1",
        "promotion_status": PROMOTION_STATUS,
        "carrier_internal": False,
        "external_gr_baseline": True,
        "calibration_required": True,
        "status": "external_gr_baseline_non_promoting",
        "scope": [
            "Mercury perihelion advance",
            "solar light deflection at limb",
            "solar Shapiro delay scale",
            "solar gravitational redshift scale",
        ],
        "constants": {
            "speed_of_light_m_per_s": SPEED_OF_LIGHT_M_PER_S,
            "solar_GM_m3_per_s2": SOLAR_GM_M3_PER_S2,
            "solar_radius_m": SOLAR_RADIUS_M,
            "astronomical_unit_m": ASTRONOMICAL_UNIT_M,
            "julian_century_days": JULIAN_CENTURY_DAYS,
            "mercury_semimajor_axis_au": MERCURY_SEMIMAJOR_AXIS_AU,
            "mercury_eccentricity": MERCURY_ECCENTRICITY,
            "shapiro_receiver_orbit_radius_au": receiver_orbit_radius_au,
        },
        "records": records,
        "decision": {
            "promotes_gravity_lane": False,
            "reason": (
                "Values are GR textbook weak-field baselines used as external "
                "calibration targets; no carrier-internal prediction is supplied."
            ),
        },
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "test_name",
        "quantity",
        "value",
        "unit",
        "formula",
        "context",
        "promotion_status",
        "carrier_internal",
        "external_gr_baseline",
        "calibration_required",
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for record in records:
            writer.writerow(
                {
                    key: str(value).lower() if isinstance(value, bool) else value
                    for key, value in record.items()
                }
            )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Emit non-promoting solar weak-field GR baseline diagnostics."
    )
    parser.add_argument("--json-output", type=Path, default=DEFAULT_JSON_OUTPUT)
    parser.add_argument("--csv-output", type=Path, default=DEFAULT_CSV_OUTPUT)
    parser.add_argument(
        "--shapiro-receiver-orbit-radius-au",
        type=float,
        default=MERCURY_SEMIMAJOR_AXIS_AU,
        help="Receiver heliocentric orbit radius for the grazing one-way Shapiro scale.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not math.isfinite(args.shapiro_receiver_orbit_radius_au) or args.shapiro_receiver_orbit_radius_au <= 0.0:
        raise SystemExit("--shapiro-receiver-orbit-radius-au must be finite and positive")

    records = build_records(args.shapiro_receiver_orbit_radius_au)
    payload = build_payload(records, args.shapiro_receiver_orbit_radius_au)
    write_json(args.json_output, payload)
    write_csv(args.csv_output, records)
    print(
        "solar weak-field GR baseline diagnostic wrote "
        f"{args.json_output} and {args.csv_output}; promotion_status={PROMOTION_STATUS}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
