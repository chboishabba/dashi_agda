#!/usr/bin/env python3
"""D'Amelio 2026 original-source schedule/filename and missingness boundary.

Original contributors own the experiment; original configuration:
tomdamelio/dmt-emotions@16067a5f config.py and tet/data_loader.py.
This adapter checks public SOURCE DESIGN and nominal filename identities;
it does not load .mat health data, establish actual sample completeness,
independent Lewis-Healey recruitment, legal/ethics authority, or M2.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "Docs/receipts/DMTDamelioOriginalDoseSessionCrosswalk20261026.json"
CONFIG_SHA = "620c77b4053b7001f3c0e2ce8a84ff94ba4d423a"
LOADER_SHA = "903ad492f6f6e8e155fb9ab115f111796c0452b6"
PREPROCESS_SHA = "eaa07bb4bc349904fc57c6a6c853681494bce57e"
CODE_COMMIT = "16067a5ff31b7f390381fc5b25b587b1769d9dd1"
DOSING = ("Alta", "Baja")
ORIGINAL_HIGH_FIRST = frozenset(("S01", "S04", "S05", "S09", "S10", "S15", "S17", "S18"))
EXPECTED = tuple("S{:02d}".format(i) for i in range(1,21) if i != 14)
PATTERN = re.compile(r"^(S[0-9]{2})_(DMT|RS)_Session([12])_([A-Za-z0-9]+)\.mat$", re.I)


def load_source(path=SOURCE):
    return json.loads(Path(path).read_text(encoding="utf8"))


def validate_source(data):
    if data.get("schema") != "dashi-dmt-damelio-source-schedule-v1":
        raise ValueError("Wrong experimental source schedule")
    orig = data["original_source"]
    if (orig.get("github_repository") != "tomdamelio/dmt-emotions"
        or orig.get("commit") != CODE_COMMIT
        or orig.get("config_git_blob_sha1") != CONFIG_SHA
        or orig.get("loader_git_blob_sha1") != LOADER_SHA
        or orig.get("preprocessor_git_blob_sha1") != PREPROCESS_SHA):
        raise ValueError("Unrecognized author-source Git identity")
    design = data["design"]
    if (design.get("total_protocol_subjects") != 19
        or design.get("source_TET_available_subjects_reported") != 18
        or design.get("physiology_joint_complete_reported") != 7
        or design.get("subject_id_exception") != "S14 absent from planned 19-subject protocol"
        or design.get("original_matrix_dimension_count") != 15
        or design.get("original_sample_interval_seconds") != 4
        or design.get("original_RS_max_seconds_exclusive") != 600
        or design.get("original_DMT_max_seconds_exclusive") != 1200
        or design.get("dose_mg_map") != {"Alta": 40, "Baja": 20}):
        raise ValueError("Original experimental design or missingness scale changed")
    rows = data["scheduled_participant_sessions"]
    if not isinstance(rows, list) or len(rows) != 19:
        raise ValueError("Source schedule not all 19 individuals")
    roster = {}
    for row in rows:
        if not isinstance(row, dict) or set(row) != {
                "id", "session_1_dose_label", "session_2_dose_label"}:
            raise ValueError("Unrecognized author-schedule row")
        pid = row["id"]
        arms = (row["session_1_dose_label"], row["session_2_dose_label"])
        if pid in roster or pid not in EXPECTED or set(arms) != set(DOSING):
            raise ValueError("Duplicated, unknown or non-crossover participant")
        roster[pid] = arms
    if set(roster) != set(EXPECTED):
        raise ValueError("Source roster differs from original")
    if {p for p, arms in roster.items() if arms[0] == "Alta"} != ORIGINAL_HIGH_FIRST:
        raise ValueError("Original 19-person dose assignments have been modified")
    expected_not_proven = (
        "raw_mat_files_accessed", "observed_participant_dose_crosswalk_replayed",
        "which_18_TET_subjects_verified", "which_7_phys_complete_verified",
        "participant_overlap_with_Lewis_Healey_crosswalk_verified",
        "subject_mat_original_rating_replayed", "zenodo_version_checksum_verified",
        "independent_agent_evidence")
    if any(data["evidence_ceiling"].get(k) is not False for k in expected_not_proven):
        raise ValueError("Documentary schedule wrongly promoted to original data")
    return roster


def parse_original_name(name, roster):
    if not isinstance(name, str) or Path(name).name != name:
        raise ValueError("Refuse paths, only original leaf filenames")
    match = PATTERN.fullmatch(name)
    if not match:
        raise ValueError("Unrecognized original TET session filename")
    pid, stage, n, suffix = match.groups()
    pid = pid.upper()
    stage = stage.upper()
    if pid not in roster:
        raise ValueError("Absent or unrecorded experimental participant")
    # The AUTHOR loader uses substring ('DMT' in whole name) for stage.
    # Avoid an RS file whose suffix would silently turn it into DMT.
    if (stage == "RS" and "DMT" in name.upper()) or (stage == "DMT" and "DMT" not in name.upper()):
        raise ValueError("Author parser would disagree with stage field")
    session = int(n)
    return {"participant": pid, "session": session, "stage": stage,
            "dose": roster[pid][session - 1], "suffix": suffix}


def audit_source(data, filenames=()):
    roster = validate_source(data)
    observed = {}
    for name in filenames:
        item = parse_original_name(name, roster)
        key = (item["participant"], item["session"], item["stage"])
        if key in observed:
            raise ValueError("Duplicate identity in original filename manifest")
        observed[key] = name
    by_person = {}
    for pid in sorted(roster):
        slots = [(pid, session, stage) for session in (1, 2) for stage in ("RS", "DMT")]
        by_person[pid] = sum(k in observed for k in slots)
    complete = [p for p in sorted(roster) if by_person[p] == 4]
    return {
        "schema": "dashi-dmt-damelio-filename-source-audit-v1",
        "original_code_participant_ids": len(roster),
        "original_code_protocol_visits": 2 * len(roster),
        "original_code_protocol_stage_slots": 4 * len(roster),
        "original_source_40mg_first_count": 8,
        "original_source_20mg_first_count": 11,
        "inspected_filename_slots": len(observed),
        "complete_filename_identity_participants": complete,
        "TET_18_participant_claim_reproduced": False,
        "source_mat_contents_loaded": False,
        "ethics_and_licence_verified": False,
        "source_condition_map_documentary_only": True,
        "observed_data_or_ontology_established": False,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--filenames-json", type=Path,
                   help="Optional JSON array of .mat leaf filenames; no .mat bytes read")
    args = p.parse_args()
    names = json.loads(args.filenames_json.read_text()) if args.filenames_json else []
    print(json.dumps(audit_source(load_source(), names), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
