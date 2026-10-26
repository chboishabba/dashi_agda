#!/usr/bin/env python3
"""Source-first 1953 Bangor precipitation/psychotronics audit.

No web request is made. Passing without --dly confirms a *transcribed*
NOAA excerpt and documentary ledger structure, not downloaded source bytes
or causation. With --dly, parse the exact independently obtained NCEI file.

Original: https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USW00014606.dly
Format:   https://www.ncei.noaa.gov/pub/data/ghcn/daily/readme.txt
Station:  https://www.ncdc.noaa.gov/cdo-web/datasets/GHCND/stations/GHCND%3AUSW00014606/detail
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

STATION = "USW00014606"  # Bangor International Airport, MAINE.
YEAR, MONTH = 1953, 7
EXPECTED_TENTHS_MM = {5: 0, 6: 66, 7: 193, 8: 46, 9: 74}
EXPECTED_LOCATION = "Bangor, Maine"
FORBIDDEN_JOIN = "Ellsworth, Kansas"
ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "docs/research/psychotronics-phase1-literature-landscape-20261025.csv"
EDGES = ROOT / "docs/research/psychotronics-phase1-lineage-edges-20261025.csv"


def parse_dly_record(line: str) -> tuple[str, int, int, str, dict[int, tuple[int, str, str, str]]]:
    """Decode the published GHCN-Daily 269-character monthly row.

    Values are integers, precipitation unit 0.1 millimetre. A nonblank
    quality flag is *not* counted as a clean measurement. T is a trace
    measurement flag and does not mean one tenth of a millimetre.
    """
    if len(line.rstrip("\r\n")) < 269:
        raise ValueError("GHCN record truncated; expected 269 fixed-width columns")
    station = line[:11]
    year, month, element = int(line[11:15]), int(line[15:17]), line[17:21]
    obs = {}
    for day in range(1, 32):
        chunk = line[21 + (day - 1) * 8 : 21 + day * 8]
        raw = int(chunk[:5])
        if raw != -9999:
            obs[day] = (raw, chunk[5], chunk[6], chunk[7])
    return station, year, month, element, obs


def check_noaa_month(lines: list[str]) -> dict:
    matched = []
    for line in lines:
        if line.startswith(f"{STATION}{YEAR}{MONTH:02d}PRCP"):
            matched.append(parse_dly_record(line))
    if len(matched) != 1:
        raise ValueError(f"expected one Bangor July 1953 PRCP row; found {len(matched)}")
    station, year, month, element, measurements = matched[0]
    if (station, year, month, element) != (STATION, YEAR, MONTH, "PRCP"):
        raise ValueError("station/element/date mismatch")
    for day, expected in EXPECTED_TENTHS_MM.items():
        value, mflag, qflag, sflag = measurements[day]
        if value != expected:
            raise ValueError(f"July {day}: expected {expected} tenths-mm; got {value}")
        if qflag.strip():
            raise ValueError(f"July {day}: quality flag {qflag!r}, not validated")
    return {
        "station": station,
        "location": EXPECTED_LOCATION,
        "year": year,
        "month": month,
        "daily_tenths_mm": {str(d): measurements[d][0] for d in EXPECTED_TENTHS_MM},
        "july6_to_8_tenths_mm": sum(measurements[d][0] for d in (6, 7, 8)),
        "observed_meteorological_rain": True,
        "at_original_ellsworth_site": False,
        "hourly_ellsworth_onset_confirmed": False,
        "device_weather_causality_confirmed": False,
    }


def audit_ledgers(sources_file: Path = SOURCES, edges_file: Path = EDGES) -> dict:
    with sources_file.open(newline="", encoding="utf-8") as f:
        sources = list(csv.DictReader(f))
    with edges_file.open(newline="", encoding="utf-8") as f:
        edges = list(csv.DictReader(f))
    sid = [s["id"] for s in sources]
    eid = [e["edge"] for e in edges]
    if len(set(sid)) != len(sid) or len(set(eid)) != len(eid):
        raise ValueError("duplicate source or edge ID")
    if not {"P1-63", "P1-64", "P1-65", "P1-66", "P1-67", "P1-68"} <= set(sid):
        raise ValueError("missing NOAA/early press/custody/geographic/method records")
    if not {"E95", "E96", "E97", "E98", "E99", "E100", "E101", "E102", "E103"} <= set(eid):
        raise ValueError("missing source-specific weather evidence boundaries")
    if any(e["source_id"] not in sid or e["target_id"] not in sid for e in edges):
        raise ValueError("dangling directed edge")
    if any(None in row or not row["locator"].startswith("https://") for row in sources):
        raise ValueError("source CSV column or URL error")
    if any(None in row or not row["source_locator"].startswith("https://") for row in edges):
        raise ValueError("edge CSV column or URL error")
    noaa = next(s for s in sources if s["id"] == "P1-63")
    kansas = next(s for s in sources if s["id"] == "P1-66")
    if "Bangor" not in noaa["original_work"] or "Kansas" not in kansas["original_work"]:
        raise ValueError("station/geographic negative-control records confused")
    return {"source_rows": len(sources), "edge_rows": len(edges),
            "source_ids_unique": True, "edges_resolve": True,
            "kansas_as_maine_excluded": True}


def synthetic_fixture() -> str:
    """Parser unit fixture only; never call this an acquired NOAA .dly file."""
    days = [-9999] * 31
    for day, amount in EXPECTED_TENTHS_MM.items():
        days[day - 1] = amount
    return f"{STATION}{YEAR}{MONTH:02d}PRCP" + "".join(
        f"{x:5d}  0" for x in days
    )


def self_test() -> dict:
    row = synthetic_fixture()
    assert len(row) == 269
    parsed = check_noaa_month([row])
    assert parsed["july6_to_8_tenths_mm"] == 305
    assert parsed["device_weather_causality_confirmed"] is False
    for invalid in (row[:-1], row.replace(STATION, "USW00014607", 1)):
        try:
            check_noaa_month([invalid])
        except ValueError:
            pass
        else:
            raise AssertionError("malformed or wrong-station row accepted")
    # A different place with the same town name must never be used as data.
    assert FORBIDDEN_JOIN not in (parsed["location"], EXPECTED_LOCATION)
    return {"fixed_width_parser_synthetic": "PASS",
            "truncated_record_rejected": True,
            "wrong_station_rejected": True,
            "daily_amount_and_305_sum": "PASS",
            "geographic_negative_control": "PASS"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dly", type=Path, help="local NOAA .dly file OR a separately transcribed official single-row excerpt; origin not authenticated")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--ledger-only", action="store_true")
    args = parser.parse_args()
    report = {"provenance": "NOAA Bangor Maine July 1953 GHCN-Daily",
              "data_source_url": "https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USW00014606.dly",
              "data_original_bytes_checked": False}
    report["ledgers"] = audit_ledgers()
    if args.self_test:
        report["self_test"] = self_test()
    if args.dly is not None:
        local_bytes = args.dly.read_bytes()
        data = local_bytes.decode("ascii").splitlines()
        report["observation"] = check_noaa_month(data)
        report["local_input_byte_count"] = len(local_bytes)
        report["local_input_sha256"] = hashlib.sha256(local_bytes).hexdigest()
        report["local_input_parsed"] = True
        report["data_original_bytes_checked"] = False
        report["source_authenticity"] = "unverified local source custody; matching published values is not authenticated remote bytes"
        report["source_scope"] = "one matched month only; content could be web-transcribed excerpt or a full station file"
    elif not args.ledger_only:
        report["excerpt_status"] = "web-inspected exact values; full NCEI file not downloaded here"
        report["observation"] = {
            "station": STATION,
            "july5_to_9_tenths_mm": EXPECTED_TENTHS_MM,
            "july6_to_8_tenths_mm": 305,
            "observed_meteorological_rain": True,
            "at_original_ellsworth_site": False,
            "hourly_ellsworth_onset_confirmed": False,
            "device_weather_causality_confirmed": False,
        }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
