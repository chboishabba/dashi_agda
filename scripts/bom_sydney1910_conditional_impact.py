#!/usr/bin/env python3
"""Source-bounded Sydney 1910 duplicated-week arithmetic, not a correction.

Reads the verbatim numeric values from the ABC-hosted, claimant-supplied CDO
PDF excerpt. Calculates conditional daily-mean sensitivity if ONE week is
later authenticated against original paper records. It cannot choose the
authentic week, infer a national trend, or prove copying from coincidence.
"""
from __future__ import annotations
import argparse
import calendar
from datetime import date, timedelta
from fractions import Fraction
import json
from pathlib import Path

DEFAULT_SOURCE = Path(__file__).resolve().parents[1] / (
    "Docs/support/reference/bom_abc_mediawatch_station_excerpts_20261026.json"
)


def exact(x):
    return Fraction(str(x))


def as_text(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"


def source_case(source):
    if source.get("schema") != "dashi.bom.abc.mediawatch.excerpts.v1":
        raise ValueError("source schema mismatch")
    matches = [c for c in source.get("cases", []) if c.get("id") == "S1910-JANFEB7"]
    if len(matches) != 1:
        raise ValueError("1910 case identity missing or ambiguous")
    case = matches[0]
    if (source.get("station_id"), source.get("variable"), case.get("left_start"),
        case.get("right_start"), case.get("product_code")) != (
            "066062", "tmin", "1910-01-25", "1910-02-01", "IDCJAC0011"):
        raise ValueError("station, date, variable or product code changed")
    if case.get("source") != "https://live-production.wcms.abc-cdn.net.au/92bea6c6ca9f85b7cbbcccff0f34ddf0":
        raise ValueError("unexpected excerpt locator")
    if any(case.get(k) != [v]*7 for k, v in (
        ("quality_flags_left", "Y"), ("quality_flags_right", "Y"),
        ("accumulation_days_left", 1), ("accumulation_days_right", 1))):
        raise ValueError("quality / accumulation receipt incomplete")
    if source.get("original_paper_records_authenticated") is not False:
        raise ValueError("this source is not an original authenticated paper ledger")
    left, right = case.get("left"), case.get("right")
    if not isinstance(left, list) or not isinstance(right, list) or len(left) != 7 or len(right) != 7:
        raise ValueError("two complete seven-day blocks required")
    original_start = [date.fromisoformat(case[k]) for k in ("left_start", "right_start")]
    if original_start != [date(1910, 1, 25), date(1910, 2, 1)]:
        raise ValueError("date mismatch")
    if date(1910, 1, 25) + timedelta(days=7) != date(1910, 2, 1):
        raise AssertionError("calendar boundary mismatch")
    observed = [exact(x) for x in left]
    if observed != [exact(x) for x in right]:
        raise ValueError("no exact match in source")
    return observed


def sensitivities(readings, hypothetical_week_mean_delta=None):
    if len(readings) != 7:
        raise ValueError("seven readings required")
    week_sum = sum(readings, Fraction(0))
    week_mean = week_sum/7
    january_days = calendar.monthrange(1910, 1)[1]
    february_days = calendar.monthrange(1910, 2)[1]
    year_days = 366 if calendar.isleap(1910) else 365
    coeff = {
        "january_if_january_original_is_wrong": Fraction(7, january_days),
        "february_if_february_original_is_wrong": Fraction(7, february_days),
        "1910_station_year_if_one_week_is_wrong": Fraction(7, year_days)
    }
    result = {
        "schema": "dashi.bom.sydney1910.conditional_sensitivity.v1",
        "observed_week_sum_C": as_text(week_sum),
        "observed_week_mean_C": as_text(week_mean),
        "observed_week_mean_decimal_C": float(week_mean),
        "numerical_match_days": 7,
        "coefficient_of_true_minus_published_week_mean": {k: as_text(v) for k, v in coeff.items()},
        "interpretation": "conditional station daily-mean sensitivity, NOT the actual observed correction",
        "original_week_identified": False,
        "paper_record_authenticated": False,
        "full_daily_series_loaded": False,
        "homogenised_ACORN_data_loaded": False,
        "national_trend_impact_computed": False,
    }
    if hypothetical_week_mean_delta is not None:
        delta = exact(hypothetical_week_mean_delta)
        result["explicitly_hypothetical_week_mean_delta_C"] = as_text(delta)
        result["explicitly_hypothetical_statistic_deltas_C"] = {
            k: as_text(v * delta) for k, v in coeff.items()
        }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--hypothetical-mean-delta", help="A declared hypothetical °C change, never assumed true")
    parser.add_argument("--output", type=Path)
    opts = parser.parse_args()
    source = json.loads(opts.source.read_text(encoding="utf-8"))
    result = sensitivities(source_case(source), opts.hypothetical_mean_delta)
    output = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if opts.output:
        opts.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
