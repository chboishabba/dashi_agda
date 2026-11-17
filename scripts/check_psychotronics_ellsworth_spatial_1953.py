#!/usr/bin/env python3
"""1953 Maine spatial GHCN documentary audit, reusing existing 269-column decoder.

Original historical observers: NOAA/NCEI custodial dataset for Bangor/Bar Harbor.
Research comparison: Johl Brown with OpenAI ChatGPT assistance. Not an
hourly weather observation, an authenticated downloaded .dly or a causal test.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from check_psychotronics_ellsworth_1953_sources import parse_dly_record

ROOT = Path(__file__).resolve().parents[1]
RECEIPTS = ROOT / "docs" / "receipts"
SITES = {
    "Bangor": ("USW00014606", "NOAABangor1953JulyPRCPWebExcerpt20261026.txt",
               {5: 0, 6: 66, 7: 193, 8: 46, 9: 74}),
    "Bar Harbor 3 NW": ("USC00170371", "NOAABarHarbor1953JulyPRCPWebExcerpt20261026.txt",
                        {5: 0, 6: 0, 7: 130, 8: 0, 9: 10}),
}

def original_line(path: Path, station: str) -> str:
    lines = [x for x in path.read_text(encoding="ascii").splitlines()
             if x.startswith(station + "195307PRCP")]
    if len(lines) != 1:
        raise ValueError(f"expected one July 1953 PRCP row for {station}")
    if len(lines[0]) != 269:
        raise ValueError("wrong 269-column original excerpt width")
    return lines[0]

def decode_checked(line: str, station: str, expected: dict[int, int]) -> dict:
    if len(line) != 269:
        raise ValueError("record is not 269 columns")
    ident, year, month, element, days = parse_dly_record(line)
    if (ident, year, month, element) != (station, 1953, 7, "PRCP"):
        raise ValueError("station, year, month or observation type mismatch")
    seen = {}
    for day, value in expected.items():
        if day not in days:
            raise ValueError(f"missing July {day}")
        actual, m, q, s = days[day]
        if actual != value:
            raise ValueError(f"July {day}: expected {value}, got {actual}")
        if q.strip():
            raise ValueError(f"July {day}: nonempty NOAA quality flag")
        seen[str(day)] = {"tenths_mm": actual, "measurement_flag": m.strip(),
                          "quality_flag": q.strip(), "source_flag": s.strip()}
    return {"station": station, "daily_5_to_9": seen,
            "july6_to_8_tenths_mm": sum(days[d][0] for d in (6, 7, 8))}

def report(receipts: Path = RECEIPTS) -> dict:
    values = {}
    for label, (station, filename, expected) in SITES.items():
        values[label] = decode_checked(original_line(receipts / filename, station),
                                       station, expected)
    bango = values["Bangor"]["july6_to_8_tenths_mm"]
    harbor = values["Bar Harbor 3 NW"]["july6_to_8_tenths_mm"]
    assert bango == 305 and harbor == 130
    return {
        "classification": "publisher-web-transcribed monthly rows, not original file-byte custody",
        "originals": [
            "https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USW00014606.dly",
            "https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USC00170371.dly"
        ],
        "data_original_full_file_downloaded": False,
        "same_custodial_network_not_same_gauge": True,
        "nearer_gauge_exact_ellsworth_site": False,
        "instrument_observation_day_cutoffs_verified": False,
        "local_ellsworth_22h_onset_proved": False,
        "weather_intervention_causality_proved": False,
        "july6_to_8_station_difference_tenths_mm": bango - harbor,
        "stations": values,
    }

def self_test() -> dict:
    baseline = report()
    assert baseline["stations"]["Bar Harbor 3 NW"]["daily_5_to_9"]["7"]["tenths_mm"] == 130
    cases = 0
    for label, (station, filename, expected) in SITES.items():
        line = original_line(RECEIPTS / filename, station)
        for bad in (line[:-1], line.replace(station, "ABCDEFGHIJK", 1),
                    line[:21 + 6 * 8] + "  999" + line[26 + 6 * 8:],
                    line[:21 + 6 * 8 + 6] + "Q" + line[21 + 6 * 8 + 7:]):
            try:
                decode_checked(bad, station, expected)
            except ValueError:
                cases += 1
            else:
                raise AssertionError(f"invalid provenance/data accepted for {label}")
    assert cases == 8
    return {"adversarial_fixtures_passed": cases, "publisher_excerpt_replay": True,
            "independence_or_causality_not_promoted": True}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    result = report()
    if args.self_test:
        result["self_test"] = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
