#!/usr/bin/env python3
"""Original NOAA OBS-TIME consumer and explicit day-boundary sensitivity audit.

NOAA/NCEI originally authored the daily values, station history, and CSV
schema. Wilhelm Reich authored the historical 1954 claims. Case-specific
analysis: Johl Brown with OpenAI ChatGPT assistance. No observed 1953
station clock or hour is invented; no weather modification is inferred.

Reads official-format per-station OR per-year unheaded eight-field GHCNd
CSV, optionally gzip-compressed, supplied separately on disk. A hash of
a local file is NOT authentication of publisher-original downloaded bytes.
"""
from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
from pathlib import Path

SITE_VALUES = {
    "USW00014606": {6: 66, 7: 193, 8: 46},   # Bangor, tenths-mm
    "USC00170371": {6: 0, 7: 130, 8: 0},     # Bar Harbor 3 NW
}
FIELDS = ("id", "date", "element", "value", "mflag", "qflag", "sflag", "obs_time")
OBSERVATION_LOCAL_MINUTE = 22 * 60  # Hypothetical 6 July 22:00 at a station
NOAA_STATION_CSV_README = "https://www.ncei.noaa.gov/pub/data/ghcn/daily/readme-by_station.txt"
NOAA_YEAR_CSV_README = "https://www.ncei.noaa.gov/pub/data/ghcn/daily/by_year/readme-by_year.txt"


def parse_clock(raw: str) -> int | None:
    """None means missing, not midnight. Format HHMM in 0..2359."""
    if raw == "":
        return None
    if len(raw) != 4 or not raw.isascii() or not raw.isdigit():
        raise ValueError("OBS-TIME is neither empty nor four ASCII digits")
    hh, mm = int(raw[:2]), int(raw[2:])
    if hh > 23 or mm > 59:
        raise ValueError("OBS-TIME out of valid civil time range")
    return hh * 60 + mm


def proposed_label_day(cutoff_minutes: int, event_minutes: int = OBSERVATION_LOCAL_MINUTE) -> int:
    """Hypothetical 6 July event's daily end-label 6 or 7.

    Assumptions only: event and cutoff on SAME LOCAL station clock,
    24-hour accumulation ending daily at cutoff, right-closed bucket.
    These assumptions are NOT independently verified for July 1953;
    neither of the two gauges is the Reich apparatus site.
    """
    if not 0 <= cutoff_minutes < 1440 or not 0 <= event_minutes < 1440:
        raise ValueError("invalid clock minutes")
    return 6 if event_minutes <= cutoff_minutes else 7


def clock_ambiguity_certificate() -> dict:
    labels = {6: [], 7: []}
    for minute in range(24 * 60):
        labels[proposed_label_day(minute)].append(minute)
    assert len(labels[6]) == 120 and len(labels[7]) == 1320
    assert labels[6][0] == 1320 and labels[7][-1] == 1319
    return {
        "synthetic_conditional_only": True,
        "possible_daily_labels_for_event_at_1953_07_06_22h": [6, 7],
        "candidate_cutoffs_label_july6": len(labels[6]),
        "candidate_cutoffs_label_july7": len(labels[7]),
        "boundary_assumption": "station-local 24-hour right-closed window",
        "historical_obs_time_recovered": False,
        "same_site_station": False,
        "independent_event_rain_or_causality_verified": False,
    }


def parse_row(row: list[str]) -> tuple[str, int, int, str | None]:
    if len(row) != 8:
        raise ValueError("GHCNd CSV requires eight fields (incl OBS-TIME)")
    sid, date, element, val, mflag, qflag, sflag, clock = row
    if len(sid) != 11 or len(date) != 8 or not date.isascii() or not date.isdigit():
        raise ValueError("invalid station/date identifier")
    if element != "PRCP":
        raise ValueError("expected PRCP")
    if qflag:
        raise ValueError("quality-flagged PRCP cannot be certified here")
    if not (val.lstrip("-").isdigit() and val.isascii()):
        raise ValueError("non-integer PRCP")
    value = int(val)
    if value < 0 or value == -9999:
        raise ValueError("missing/negative PRCP")
    return sid, int(date), value, clock or None


def read_1953_rows(path: Path) -> dict:
    """Stream gzip/plain original-format GHCNd; reject duplicate conflicting days.

    A local file can be a later transform/mirror. Provenance and byte custody
    must be established independently of successful CSV parsing or hashing.
    """
    results: dict[str, dict[int, dict]] = {sid: {} for sid in SITE_VALUES}
    opener = gzip.open if path.suffix.lower() == ".gz" else open
    with opener(path, "rt", encoding="ascii", newline="") as f:
        for row in csv.reader(f):
            if not row or row[0] not in SITE_VALUES or len(row) < 3:
                continue
            if row[1] not in ("19530706", "19530707", "19530708") or row[2] != "PRCP":
                continue
            sid, date, value, clock = parse_row(row)
            day = date % 100
            if day in results[sid]:
                raise ValueError("duplicate station-day PRCP row")
            if value != SITE_VALUES[sid][day]:
                raise ValueError(f"CSV/dly precipitation mismatch: {sid} July {day}")
            if clock is not None:
                parse_clock(clock)
            results[sid][day] = {
                "tenths_mm": value,
                "obs_time": clock,
                "clock_status": "publisher_CSV_field_present" if clock else "not_recorded_in_CSV",
            }
    present = {sid: days for sid, days in results.items() if days}
    if not present:
        raise ValueError("no requested July 1953 PRCP observations in CSV")
    for sid, days in present.items():
        if set(days) != {6, 7, 8}:
            raise ValueError(f"incomplete requested July 1953 station: {sid}")
    return present


def merge_1953_rows(paths: list[Path]) -> dict:
    """Permit one original by_year file or separate original by_station files."""
    merged = {}
    for path in paths:
        for sid, days in read_1953_rows(path).items():
            if sid in merged:
                raise ValueError(f"duplicate station across inputs: {sid}")
            merged[sid] = days
    return merged


def sha256_local(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for buf in iter(lambda: f.read(1048576), b""):
            h.update(buf)
    return h.hexdigest()


def report(paths: list[Path] | None = None) -> dict:
    result = {
        "purpose": "historical observation-clock acquisition discriminator",
        "original_agency": "NOAA/NCEI GHCN-Daily and HOMR",
        "site_day_values_tenths_mm": SITE_VALUES,
        "clock_sensitivity": clock_ambiguity_certificate(),
        "source_format_docs": [NOAA_STATION_CSV_README, NOAA_YEAR_CSV_README],
        "full_original_dataset_publisher_byte_custody_verified": False,
        "historical_same_site_hourly_Ellsworth_verified": False,
        "reich_device_weather_causality_verified": False,
    }
    if not paths:
        result["clock_acquisition_status"] = "not_acquired"
    else:
        result["clock_acquisition_status"] = "provided_local_CSV_parsed_not_publisher_authenticated"
        result["local_input_sha256"] = {str(path): sha256_local(path) for path in paths}
        result["station_day_rows"] = merge_1953_rows(paths)
        result["missing_station_clock_sources"] = sorted(set(SITE_VALUES) - set(result["station_day_rows"]))
        result["time_claim_limit"] = "OBS-TIME from NOAA/HOMR if present; not independent weather hour or site."
    return result


def self_test() -> dict:
    assert parse_clock("") is None
    assert parse_clock("0000") == 0
    assert parse_clock("0700") == 420
    assert parse_clock("2200") == 1320
    assert proposed_label_day(420) == 7 and proposed_label_day(1380) == 6
    assert clock_ambiguity_certificate()["candidate_cutoffs_label_july7"] == 1320
    for bad in ("2400", "2360", "9999", "7AM", "070", "０７００"):
        try:
            parse_clock(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid observation clock accepted")
    for bad in (-1, 1440):
        try:
            proposed_label_day(bad)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid cutoff accepted")
    for sid, vals in SITE_VALUES.items():
        for day, expected in vals.items():
            row = [sid, f"195307{day:02d}", "PRCP", str(expected), "", "", "0", ""]
            assert parse_row(row) == (sid, 19530700 + day, expected, None)
    return {"passed": True, "synthetic_fixtures": True, "original_1953_obs_time_claimed": False}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ghcnd-csv", action="append", type=Path, help="repeat for local by_station or by_year .csv[.gz]")
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    output = report(a.ghcnd_csv)
    if a.self_test:
        output["self_test"] = self_test()
    print(json.dumps(output, indent=2, sort_keys=True))
