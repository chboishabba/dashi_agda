#!/usr/bin/env python3
"""Emit ranked reference traces for the ungated twenty-scientist composite applications.

The Agda owners remain authoritative.  This script mirrors the currently
ungated application/proof-debt topology and ranks soft residuals for acquisition
or replay work.  It never upgrades source strength or engineering qualification.
"""

from __future__ import annotations

import argparse
import json
from typing import Any

SOFT_RESIDUAL_WEIGHTS = {
    "source_replay": 5,
    "qualification": 4,
    "validation": 4,
    "operating_window": 4,
    "calibration": 4,
    "custody": 2,
}

TRACES = {
    "long_duration_science_platform": [
        {"owner": "Frank W. Maiwald", "kind": "source_replay", "missing": "raw action-spectrum intensity/calibration data"},
        {"owner": "Zhou Guangyuan", "kind": "source_replay", "missing": "multi-sample aerogel synthesis/property table"},
        {"owner": "Joshua Kyle LeBlanc", "kind": "qualification", "missing": "named device qualification, calibration and failure evidence"},
        {"owner": "Monica Jacinto / Monica Reza", "kind": "operating_window", "missing": "MONDALOY/enamel descendant operating and qualification window"},
        {"owner": "Zhang Daibing", "kind": "validation", "missing": "one source-exact autonomy/control replay"},
        {"owner": "Nuno F. G. Loureiro", "kind": "custody", "missing": "Viriato repository/simulation-state handover"},
    ],
    "autonomous_remote_survey_platform": [
        {"owner": "Zhang Xiaoxin", "kind": "source_replay", "missing": "forecast whitening/CEEMDAN/CWT hyperparameters, code and data"},
        {"owner": "Carl J. Grillmair", "kind": "source_replay", "missing": "source survey slice, matched-filter weights and orbit uncertainty"},
        {"owner": "Michael David Hicks", "kind": "source_replay", "missing": "source lightcurve, viewing geometry and calibration"},
        {"owner": "Feng Yanghe", "kind": "source_replay", "missing": "source classifier equations, data and label-noise parameters"},
        {"owner": "Chen Shuming", "kind": "validation", "missing": "source hardware-verification graph, stimuli, coverage and mismatch example"},
        {"owner": "Zhang Daibing", "kind": "validation", "missing": "source dynamics, gains, sensor model, geometry and error series"},
        {"owner": "Liu Donghao", "kind": "qualification", "missing": "authored DSMM maturity levels, scoring semantics and assessed example"},
    ],
}


def _rank(residuals: list[dict[str, str]]) -> list[dict[str, Any]]:
    enriched = [
        {**item, "weight": SOFT_RESIDUAL_WEIGHTS[item["kind"]]}
        for item in residuals
    ]
    return sorted(enriched, key=lambda item: (-item["weight"], item["owner"], item["missing"]))


def trace_for(application: str) -> dict[str, Any]:
    ranked = _rank(TRACES[application])
    return {
        "application": application,
        "hard_gate_count": 0,
        "ranked_soft_residuals": ranked,
        "highest_alpha": ranked[:3],
        "operational_qualification_paid": False,
        "source_replication_paid": False,
        "historical_deployment_paid": False,
        "roster_collaboration_paid": False,
        "event_cause_paid": False,
        "formal_owner": "DASHI.Culture.MissingDeceasedTwentyScientistCompositeReferenceTraceExact",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--application", choices=sorted(TRACES), default="long_duration_science_platform")
    parser.add_argument("--all", action="store_true")
    args = parser.parse_args()
    payload = (
        {name: trace_for(name) for name in sorted(TRACES)}
        if args.all
        else trace_for(args.application)
    )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
