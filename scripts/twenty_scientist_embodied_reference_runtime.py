#!/usr/bin/env python3
"""Reference planner for the twenty-scientist embodied capability BIDI.

The Agda owners remain authoritative.  This script mirrors only the public
application/role topology so an operator can inspect which science fibres are
reference-runnable and which reverse evidence leaves remain open.
"""

from __future__ import annotations

import argparse
import json
from typing import Any

SLOTS = {
    "Nuno F. G. Loureiro": {"role": "plasma_model", "ready": True, "source_replay": False, "gate": None},
    "Joshua Kyle LeBlanc": {"role": "harsh_environment_power_control", "ready": True, "source_replay": False, "gate": None},
    "Frank W. Maiwald": {"role": "molecular_diagnostics", "ready": True, "source_replay": True, "gate": None},
    "Monica Jacinto / Monica Reza": {"role": "oxygen_service_materials", "ready": True, "source_replay": False, "gate": None},
    "Carl J. Grillmair": {"role": "astronomical_inference", "ready": True, "source_replay": False, "gate": None},
    "Michael David Hicks": {"role": "planetary_characterisation", "ready": True, "source_replay": False, "gate": None},
    "William Neil McCasland": {"role": "resilient_structure_control", "ready": True, "source_replay": False, "gate": None},
    "Anthony Chavez": {"role": "accelerator_diagnostics", "ready": False, "source_replay": False, "gate": "same-person identity weld"},
    "Jason R. Thomas": {"role": "chemical_biology_assays", "ready": True, "source_replay": False, "gate": None},
    "Amy Eskridge": {"role": "anomalous_force_discrimination", "ready": False, "source_replay": False, "gate": "Amy-authored/recorded technical object"},
    "Ning Li": {"role": "precision_force_metrology", "ready": True, "source_replay": False, "gate": None},
    "Chen Shuming": {"role": "hardware_verification", "ready": True, "source_replay": False, "gate": None},
    "Feng Yanghe": {"role": "robust_decision_support", "ready": True, "source_replay": False, "gate": None},
    "Zhou Guangyuan": {"role": "thermal_protection", "ready": True, "source_replay": False, "gate": None},
    "Liu Donghao": {"role": "data_security_governance", "ready": True, "source_replay": False, "gate": None},
    "Zhang Xiaoxin": {"role": "space_weather_forecasting", "ready": True, "source_replay": True, "gate": None},
    "Zhang Daibing": {"role": "autonomous_mobility", "ready": True, "source_replay": False, "gate": None},
    "Li Minyong": {"role": "photochemical_control", "ready": True, "source_replay": False, "gate": None},
    "Fang Daining": {"role": "adaptive_structural_waves", "ready": True, "source_replay": True, "gate": None},
    "Yan Hong": {"role": "high_speed_flow_control", "ready": True, "source_replay": True, "gate": None},
}

APPLICATIONS = {
    "long_duration_science_platform": {
        "roles": [
            "plasma_model", "harsh_environment_power_control", "molecular_diagnostics",
            "oxygen_service_materials", "astronomical_inference", "planetary_characterisation",
            "resilient_structure_control", "thermal_protection", "data_security_governance",
            "space_weather_forecasting", "autonomous_mobility", "adaptive_structural_waves",
        ],
        "reverse_needs": [
            "power/control qualification", "thermal/material operating windows",
            "instrument calibration", "autonomy validation", "environment forecast validation",
            "data-governance integration", "successor/custody receipts",
        ],
    },
    "extreme_environment_research_testbed": {
        "roles": [
            "harsh_environment_power_control", "oxygen_service_materials", "accelerator_diagnostics",
            "precision_force_metrology", "hardware_verification", "thermal_protection",
            "adaptive_structural_waves", "high_speed_flow_control",
        ],
        "reverse_needs": [
            "test geometry", "calibration state", "failure history", "material qualification",
            "diagnostic validation", "flow-control operating window",
        ],
    },
    "autonomous_remote_survey_platform": {
        "roles": [
            "astronomical_inference", "planetary_characterisation", "resilient_structure_control",
            "hardware_verification", "robust_decision_support", "data_security_governance",
            "space_weather_forecasting", "autonomous_mobility",
        ],
        "reverse_needs": [
            "sensor/actuator geometry", "navigation/control validation", "processor verification",
            "survey calibration", "forecast uncertainty", "data-security workflow",
        ],
    },
    "multi_domain_research_laboratory": {
        "roles": [
            "molecular_diagnostics", "chemical_biology_assays", "anomalous_force_discrimination",
            "precision_force_metrology", "photochemical_control", "hardware_verification",
            "data_security_governance",
        ],
        "reverse_needs": [
            "spectroscopy calibration", "assay validation", "precision null-test controls",
            "molecular probe calibration", "hardware/data provenance",
        ],
    },
}


def plan_for(application: str) -> dict[str, Any]:
    spec = APPLICATIONS[application]
    role_to_people: dict[str, list[dict[str, Any]]] = {}
    for person, slot in SLOTS.items():
        role_to_people.setdefault(slot["role"], []).append({"person": person, **slot})

    selected: list[dict[str, Any]] = []
    uncovered_roles: list[str] = []
    gated: list[dict[str, Any]] = []
    for role in spec["roles"]:
        candidates = role_to_people.get(role, [])
        if not candidates:
            uncovered_roles.append(role)
            continue
        selected.extend(candidates)
        gated.extend(candidate for candidate in candidates if not candidate["ready"])

    return {
        "application": application,
        "required_roles": spec["roles"],
        "selected_slots": selected,
        "uncovered_roles": uncovered_roles,
        "gated_slots": gated,
        "reverse_needs": spec["reverse_needs"],
        "reference_runnable_slot_count": sum(1 for slot in SLOTS.values() if slot["ready"]),
        "source_replay_slot_count": sum(1 for slot in SLOTS.values() if slot["source_replay"]),
        "formal_semantics_defined": False,
        "source_replication_paid": False,
        "historical_deployment_paid": False,
        "roster_collaboration_paid": False,
        "event_cause_paid": False,
        "formal_owner": "DASHI.Culture.MissingDeceasedTwentyScientistEmbodiedReferenceRuntimeBidiExact",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--application",
        choices=sorted(APPLICATIONS),
        default="long_duration_science_platform",
        help="composite application to compile into roles and reverse evidence needs",
    )
    parser.add_argument("--all", action="store_true", help="emit plans for all composite applications")
    args = parser.parse_args()

    if args.all:
        payload = {name: plan_for(name) for name in sorted(APPLICATIONS)}
    else:
        payload = plan_for(args.application)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
