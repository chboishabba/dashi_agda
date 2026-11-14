#!/usr/bin/env python3
"""2-D spatial optical path-energy proxy from actual Kozyrev HTML ray events.

Power-weighted ray path sampled on a uniform grid. Not 3-D irradiance,
physical dose, EM enhancement, or coherent WGM. The event-producer remains
the single source of geometric collision data. Authorship: Kozyrev PR #1404.
"""
import argparse
import json
import math

C = 299792458.0

def occupancy(receipt, bins=80, extent=None):
    if receipt.get("schema") != "kozyrev-optical-events/1":
        raise ValueError("expected source-owned HTML event receipt")
    scene = receipt["scene"]
    g = scene["geometry"]
    input_power = scene["tracer"]["watt"]
    if extent is None:
        extent = 1.02 * (g["inner"] + g["growth"] * 2 * math.pi * g["turns"] + g["thick"] / 2)
    if extent <= 0 or bins < 2:
        raise ValueError("invalid grid")
    cell = 2*extent/bins
    grid = [[0.0 for _ in range(bins)] for _ in range(bins)]
    entered = 0.0
    unresolved = 0.0
    for ray in receipt["rays"]:
        if ray["gate"] != "INTERIOR_ENTRY":
            continue
        power = float(ray["source"]["power_w"])
        entered += power
        point = ray["source"]["point"]
        for event in [*ray["hits"], ray["terminal"]]:
            next_point = event["point"]
            distance = math.dist(point, next_point)
            if distance:
                steps = max(1, math.ceil(distance/(cell/3)))
                for index in range(steps):
                    fraction = (index+.5)/steps
                    x = point[0]+fraction*(next_point[0]-point[0])
                    y = point[1]+fraction*(next_point[1]-point[1])
                    ix = int((x+extent)/cell)
                    iy = int((y+extent)/cell)
                    if 0 <= ix < bins and 0 <= iy < bins:
                        grid[iy][ix] += power*distance/steps/C
            power = event.get("power_after_w", event.get("power_w", power))
            point = next_point
        if ray["terminal"]["kind"] in ("unresolved", "bounded"):
            unresolved += ray["terminal"]["power_w"]
    energy = sum(sum(row) for row in grid)
    return dict(
        schema="kozyrev-optical-occupancy/1", grid_J=grid,
        grid_size=bins, half_extent_m=extent, entered_W=entered,
        unresolved_W=unresolved, equivalent_energy_J=energy,
        input_normalised_residence_ns=energy/input_power*1e9,
        evidence="Numerical 2-D ray occupancy proxy; not EM mode or human exposure")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("events")
    parser.add_argument("--bins", type=int, default=80)
    args = parser.parse_args()
    with open(args.events, encoding="utf-8") as file:
        result = occupancy(json.load(file), args.bins)
    print(json.dumps(result))
