#!/usr/bin/env python3
"""Fail-closed synthetic TET source-contract for DMT presence-onset proposals.

Original empirical/workflow source: D'Amelio et al. (2026, in preparation),
'tomdamelio/dmt-emotions' @ 16067a5ff31b7f390381fc5b25b587b1769d9dd1.
The 15-dimensional scale/4-second TET descriptions are original source code,
NOT results reproduced by DASHI. Coding is retrospective, not a live observer.
Scientific comparison requires rights, protocol mapping, cohort independence,
validation against raw measurements, and prospective model restrictions.

This intentionally REJECTS human-data imports until a separate audited
research-data adapter exists. Its synthetic event timing is an experiment
DESIGN witness, not a finding about external autonomous entities.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from pathlib import Path

CODE_COMMIT = "16067a5ff31b7f390381fc5b25b587b1769d9dd1"
CONFIG_BLOB = "620c77b4053b7001f3c0e2ce8a84ff94ba4d423a"
SCHEMA = "dashi-dmt-tet-presence-synthetic-v1"
DIMENSIONS = (
    "pleasantness", "unpleasantness", "emotional_intensity",
    "elementary_imagery", "complex_imagery", "auditory",
    "interoception", "bliss", "anxiety", "entity", "selfhood",
    "disembodiment", "salience", "temporality", "general_intensity"
)
CHANNELS = ("elementary_imagery", "complex_imagery", "entity")
TOP = {"schema", "mode", "code_commit", "config_blob", "source_id",
       "interval_seconds", "dimensions", "threshold", "samples"}
SAMPLE = {"person", "dose_mg", "stage", "time_index", "values"}


def _number(value):
    if not isinstance(value, str) or not value.strip():
        raise ValueError("Retrospective ratings must be exact decimal strings")
    try:
        v = Fraction(value)
    except (ValueError, ZeroDivisionError) as e:
        raise ValueError("Invalid retrospective rating") from e
    if not (0 <= v <= 10):
        raise ValueError("Rating outside original scale 0 to 10")
    return v


def validate(doc):
    if not isinstance(doc, dict) or set(doc) != TOP:
        raise ValueError("Unknown data/schema fields; do not pass raw human records")
    if (doc["schema"] != SCHEMA or doc["mode"] != "synthetic"
            or not isinstance(doc["source_id"], str)
            or not doc["source_id"].startswith("synthetic:")
            or doc["code_commit"] != CODE_COMMIT
            or doc["config_blob"] != CONFIG_BLOB
            or doc["interval_seconds"] != 4
            or doc["dimensions"] != list(DIMENSIONS)):
        raise ValueError("Unreviewed TET source, scale, or modality")
    threshold = _number(doc["threshold"])
    if threshold == 0:
        raise ValueError("Zero onset threshold would count baseline absence")
    samples = doc["samples"]
    if not isinstance(samples, list) or not samples:
        raise ValueError("No timestamped synthetic observations")
    groups = defaultdict(list)
    people = set()
    for item in samples:
        if not isinstance(item, dict) or set(item) != SAMPLE:
            raise ValueError("Unknown sample fields / prohibited raw narrative")
        person = item["person"]
        if not isinstance(person, str) or not person.startswith("toy-person-"):
            raise ValueError("Not an explicitly synthetic person identifier")
        people.add(person)
        if type(item["dose_mg"]) is not int or item["dose_mg"] not in (20, 40):
            raise ValueError("Source regimen is 20mg or 40mg")
        if item["stage"] not in ("RS", "DMT"):
            raise ValueError("Source stage is RS baseline or post-DMT")
        t = item["time_index"]
        if type(t) is not int or t < 0:
            raise ValueError("Invalid 4-second bin index")
        values = item["values"]
        if not isinstance(values, dict) or set(values) != set(DIMENSIONS):
            raise ValueError("Every coded sample needs the 15 declared dimensions")
        for value in values.values():
            _number(value)
        groups[(person, item["dose_mg"], item["stage"])].append(item)
    if len(people) < 2:
        raise ValueError("Synthetic fixture must have at least two distinct people")
    for person in people:
        for dose in (20, 40):
            for stage in ("RS", "DMT"):
                items = groups.get((person, dose, stage), [])
                idx = [item["time_index"] for item in items]
                if not idx or sorted(idx) != list(range(len(idx))):
                    raise ValueError("Incomplete or duplicate within-person 4s bin sequence")
    return threshold, groups


def _first_crossing(items, field, threshold):
    return next((item["time_index"] * 4 for item in sorted(items, key=lambda x: x["time_index"])
                 if _number(item["values"][field]) >= threshold), None)


def audit(doc):
    threshold, groups = validate(doc)
    results = []
    for (person, dose, stage), items in sorted(groups.items()):
        if stage != "DMT":
            continue
        onset = {key: _first_crossing(items, key, threshold) for key in CHANNELS}
        entity = onset["entity"]
        complex_ = onset["complex_imagery"]
        results.append({
            "person": person, "dose_mg": dose,
            "onset_seconds": onset,
            "entity_minus_complex_imagery_seconds": (
                entity - complex_ if entity is not None and complex_ is not None else None),
            "not_observed_is_not_zero": True,
        })
    return {
        "schema": "dashi-dmt-tet-synthetic-onset-audit-v1",
        "source_code_commit": CODE_COMMIT,
        "original_data_analysed": False,
        "independent_study_reproduction": False,
        "hypothesis": "predeclared threshold lead-lag, not direction of causation",
        "retrospective_reconstruction_and_coding_bias_remain": True,
        "external_agent_ontology_inferred": False,
        "threshold": str(threshold),
        "groups": results,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("synthetic_input", type=Path)
    a = p.parse_args()
    print(json.dumps(audit(json.loads(a.synthetic_input.read_text())), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
