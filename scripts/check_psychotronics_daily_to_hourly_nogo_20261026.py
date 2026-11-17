#!/usr/bin/env python3
"""Exact finite DAILY->HOURLY and treatment-effect nonidentifiability witnesses.

Case-specific consumer of existing NOAA spatial + revisable-evidence owners.
This is mathematics on published daily records and hypothetical potential
outcomes, not a reconstruction of observed 1953 hourly rain or a mechanism test.

Historical source authors: NOAA/NCEI (GHCN data/schema), Wilhelm Reich (1954
claimed chronology). Case comparison/formalisation: Johl Brown, with OpenAI
ChatGPT assistance. Preserve these distinct original source roles.
"""
from __future__ import annotations

import argparse
import json

from check_psychotronics_ellsworth_spatial_1953 import report
from check_psychotronics_revisable_sources_20261026 import WORLD, assess


def hourly_allocation(total_tenths_mm: int, hour: int) -> tuple[int, ...]:
    """One *hypothetical* 24-bin profile compatible with a nonnegative total."""
    if total_tenths_mm < 0 or not 0 <= hour < 24:
        raise ValueError("invalid total/hour for synthetic 24-bin allocation")
    bins = [0] * 24
    bins[hour] = total_tenths_mm
    return tuple(bins)


def noninjective_daily_projection(total_tenths_mm: int) -> dict:
    """Construct different hourly inputs with identical sum; do not infer cutoff.

    Even assuming for argument that a GHCN daily bucket is midnight-to-midnight,
    its positive amount does not identify which hour received rain. Actual
    historical station observation cutoffs were not checked here.
    """
    if total_tenths_mm <= 0:
        raise ValueError("positive daily amount required for two distinct profiles")
    early = hourly_allocation(total_tenths_mm, 1)
    late = hourly_allocation(total_tenths_mm, 23)
    assert early != late
    assert sum(early) == sum(late) == total_tenths_mm
    return {
        "synthetic_only": True,
        "total_tenths_mm": total_tenths_mm,
        "different_hourly_allocations_same_daily_total": True,
        "early_nonzero_hour": 1,
        "late_nonzero_hour": 23,
        "assumed_day_boundary_for_counterexample_only": "00:00 to 24:00",
        "actual_historical_observation_cutoff_verified": False,
    }


def counterfactual_witness() -> dict:
    """Two potential-outcome worlds agree on treated outcome, disagree on effect.

    Stronger-than-record concession: stipulate a verified treated rain event at
    the intervention site. Even THAT plus temporal order would not identify
    what would have happened without intervention. Real at-site hour is unpaid.
    """
    rain_with_intervention = 1
    spontaneous_rain_world = {"Y0": 1, "Y1": rain_with_intervention}
    attributable_rain_world = {"Y0": 0, "Y1": rain_with_intervention}
    assert spontaneous_rain_world["Y1"] == attributable_rain_world["Y1"]
    assert (attributable_rain_world["Y1"] - attributable_rain_world["Y0"]) == 1
    assert (spontaneous_rain_world["Y1"] - spontaneous_rain_world["Y0"]) == 0
    return {
        "synthetic_only": True,
        "stipulated_observation": "Y(1)=1: rain at treated site (NOT established for Reich event)",
        "same_observed_treated_outcome": True,
        "compatible_causal_effects": [0, 1],
        "unique_causal_attribution_possible": False,
        "actual_1953_counterfactual_observed": False,
    }


def case_report() -> dict:
    s = report()  # existing original NOAA fixed-width/flag validator
    with WORLD.open(encoding="utf-8") as f:
        w = json.load(f)
    initial = assess(w)
    bangor = s["stations"]["Bangor"]["daily_5_to_9"]
    harbor = s["stations"]["Bar Harbor 3 NW"]["daily_5_to_9"]
    assert [bangor[str(i)]["tenths_mm"] for i in (6, 7, 8)] == [66, 193, 46]
    assert [harbor[str(i)]["tenths_mm"] for i in (6, 7, 8)] == [0, 130, 0]
    assert initial["maine_two_station_6to8_spatial_difference"] == "station_comparison_only"
    assert initial["reich_device_caused_rain"] == "unpaid"
    assert s["data_original_full_file_downloaded"] is False
    b = s["stations"]["Bangor"]["july6_to_8_tenths_mm"]
    h = s["stations"]["Bar Harbor 3 NW"]["july6_to_8_tenths_mm"]
    assert (b, h, b - h) == (305, 130, 175)
    return {
        "source_scope": "same NOAA custodian; two distinct gauge sites; source-original full file byte custody unverified",
        "bangor_6_to_8_tenths_mm": b,
        "bar_harbor_6_to_8_tenths_mm": h,
        "between_site_difference_tenths_mm": b - h,
        "bar_harbor_july_6_daily_value": harbor["6"]["tenths_mm"],
        "hourly_inference": noninjective_daily_projection(bangor["6"]["tenths_mm"]),
        "second_station_hourly_inference": noninjective_daily_projection(harbor["7"]["tenths_mm"]),
        "counterfactual": counterfactual_witness(),
        "ellsworth_22h_local_rain_verified": False,
        "weather_front_map_page_examined": False,
        "device_caused_rain_verified": False,
    }


def self_test() -> dict:
    r = case_report()
    w = json.loads(WORLD.read_text(encoding="utf-8"))
    base = assess(w)
    assertions = 0
    # Station correction should reopen dependent same-object comparison only.
    for withdrawn, reopen, preserve in (
        ("P1-63", "bangor_daily_rain_6to8", "bar_harbor_daily_rain_6to8"),
        ("P1-71", "bar_harbor_daily_rain_6to8", "bangor_daily_rain_6to8"),
        ("P1-48", "reich_1953_reported_operation", "bangor_daily_rain_6to8"),
    ):
        edited = assess(w, {withdrawn})
        assert edited[reopen] == "reopen" and edited[preserve] == base[preserve]
        if withdrawn != "P1-48":
            assert edited["maine_two_station_6to8_spatial_difference"] == "reopen"
        else:
            assert edited["maine_two_station_6to8_spatial_difference"] == base["maine_two_station_6to8_spatial_difference"]
        assert edited["reich_device_caused_rain"] == "unpaid"
        assertions += 1
    edited = assess(w, {"P1-68"})
    assert edited["bangor_daily_rain_6to8"] == "reopen"
    assert edited["bar_harbor_daily_rain_6to8"] == "reopen"
    assertions += 1
    for wrong in (-1,):
        for hour in (0, 23):
            try:
                hourly_allocation(wrong, hour)
            except ValueError:
                assertions += 1
            else:
                raise AssertionError("negative synthetic rainfall accepted")
    for hour in (-1, 24):
        try:
            hourly_allocation(13, hour)
        except ValueError:
            assertions += 1
        else:
            raise AssertionError("hour outside 0..23 accepted")
    assert r["counterfactual"]["compatible_causal_effects"] == [0, 1]
    return {"assertions": assertions + 1, "passed": True, "physical_validation_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    result = case_report()
    if args.self_test:
        result["self_test"] = self_test()
    print(json.dumps(result, indent=2, sort_keys=True))
