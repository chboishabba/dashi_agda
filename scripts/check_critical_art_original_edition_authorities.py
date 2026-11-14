#!/usr/bin/env python3
"""Check independently located original distributor/government edition metadata.

Checks schema, original authorities, work-specific edition identities and
cross-edition separation. Public links are bibliographic locators, not
cryptographic proof that a film copy was reviewed. This script performs no
network requests and cannot authenticate the referenced webpages.
"""
import argparse
import copy
import json
from pathlib import Path

PATH = Path(__file__).resolve().parents[1] / "Docs/research/critical_art_original_edition_authorities_20261109.json"
EXPECTED = {
    "leon_au_1994_110": ("leon_1994", 6600, "00719356198E", "https://www.classification.gov.au/titles/leon-12"),
    "leon_gaumont_1996_133": ("leon_1994", 7980, "Gaumont Léon (version longue)", "https://www.gaumont.com/en/movie/leon-version-longue"),
    "dont_look_up_au_2021_138": ("dont_look_up_2021", 8280, "294721", "https://www.classification.gov.au/titles/dont-look-1"),
    "planet_of_humans_apple_2020_100": ("planet_of_the_humans_2020", 6000, "umc.cmc.2f8w1eeetfqqpettlfx80jkh9", "https://tv.apple.com/au/movie/planet-of-the-humans/umc.cmc.2f8w1eeetfqqpettlfx80jkh9"),
}

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def check(data):
    require(data.get("schema") == "dashi.critical_art.edition_external_authority.v1", "schema")
    rows = data.get("edition_records", [])
    byid = {r["edition_id"]: r for r in rows}
    require(len(rows) == len(EXPECTED) == len(byid) and set(byid) == set(EXPECTED), "edition identities")
    for key, (work, duration, record, url) in EXPECTED.items():
        row = byid[key]
        require((row["work_id"], row["duration_seconds"], row["record_id"], row["source_url"]) == (work, duration, record, url), "source-specific metadata mismatch " + key)
        require(type(row["duration_seconds"]) is int and row["duration_seconds"] > 0, "duration")
        require(row["evidence_grade"] in ("institutional_edition_metadata", "producer_edition_metadata", "distributor_edition_metadata"), "evidence grade")
        require(row["scene_verified"] is False, "metadata promoted to scene proof")
        require(bool(row["creator"].strip()), "original creators omitted")
        require(bool(row["source_kind"].strip()), "authority type omitted")
    require(byid["leon_au_1994_110"]["duration_seconds"] != byid["leon_gaumont_1996_133"]["duration_seconds"], "different cut durations erased")
    return dict(original_authority_edition_records=len(rows), distinct_leon_editions=2, authenticated_scene_observations=0, causal_audience_effects=0)

def self_test(data):
    positive = check(data)
    for label, mutate in [
        ("duplicate", lambda d: d["edition_records"].append(copy.deepcopy(d["edition_records"][0]))),
        ("false_scene", lambda d: d["edition_records"][0].update(scene_verified=True)),
        ("merge_cuts", lambda d: d["edition_records"][1].update(duration_seconds=6600)),
        ("wrong_edition_owner", lambda d: d["edition_records"][2].update(work_id="leon_1994")),
        ("source_replacement", lambda d: d["edition_records"][3].update(source_url="https://example.org")),
    ]:
        changed = copy.deepcopy(data)
        mutate(changed)
        try:
            check(changed)
        except (ValueError, KeyError, TypeError):
            pass
        else:
            raise AssertionError("negative control admitted: " + label)
    return dict(positive, negative_controls=5)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    source = json.loads(PATH.read_text(encoding="utf-8"))
    print(json.dumps(self_test(source) if args.self_test else check(source), sort_keys=True, indent=2))
