#!/usr/bin/env python3
"""Confinement and circulating-flux diagnostics from actual HTML event JSON.

Conventional 2D power-weighted geometric-optics proxy. Not EM mode Q,
a physical-field measurement, or a kernel theorem. An exterior or
unresolved trajectory is explicitly tagged, never renamed as trapped.
Original event-analysis implementation belongs to DASHI PR #1404;
optical-resonator results and classical ray laws retain prior authorship.
"""
import argparse
import json
import math

C = 299792458.0

def disk_segment_length(a, b, radius):
    """Exact Euclidean length of the closed segment inside a disk."""
    x, y = a
    dx, dy = b[0] - x, b[1] - y
    aa = dx*dx + dy*dy
    if aa == 0:
        return 0.
    bb = 2*(x*dx+y*dy)
    discriminant = bb*bb-4*aa*(x*x+y*y-radius*radius)
    if discriminant < 0:
        return math.sqrt(aa) if x*x+y*y <= radius*radius else 0.
    root = math.sqrt(max(0., discriminant))
    left = max(0.,(-bb-root)/(2*aa))
    right = min(1.,(-bb+root)/(2*aa))
    return math.sqrt(aa)*max(0.,right-left)

def analyse(data):
    if data.get("schema") != "kozyrev-optical-events/1":
        raise ValueError("expected actual HTML event receipt")
    scene = data["scene"]
    g = scene["geometry"]
    tr = scene["tracer"]
    r = max(.01, g["inner"]+g["growth"]*2*math.pi*g["turns"]+g["thick"]/2)*1.02
    incident = float(tr["watt"])
    entered = 0.
    weighted = 0.
    angular_weighted = 0.
    pending = 0.
    statuses = {}
    for ray in data["rays"]:
        source = ray["source"]
        p = source["point"]
        power = source["power_w"]
        valid = ray["gate"] == "INTERIOR_ENTRY"
        if valid:
            entered += power
        events = ray["hits"] + [{"point": ray["terminal"]["point"], "power_after_w": None}]
        for event in events:
            q = event["point"]
            length = disk_segment_length(p,q,r)
            if valid and length:
                weighted += power * length
                dx,dy=q[0]-p[0],q[1]-p[1]
                total=math.hypot(dx,dy)
                if total:
                    angular_weighted += power*length*(p[0]*dy-p[1]*dx)/total/r
            if event["power_after_w"] is not None:
                power = event["power_after_w"]
            p = q
        terminal = ray["terminal"]
        kind = terminal["kind"]
        statuses[kind]=statuses.get(kind,0)+1
        if kind in ("unresolved","bounded"):
            pending += terminal["power_w"]
    return {
        "source_W":incident, "entered_W":entered,
        "entry_fraction":entered/incident if incident else None,
        "measurement_disk_radius_m":r,
        "power_weighted_path_Wm":weighted,
        "equivalent_ray_energy_J":weighted/C,
        "input_normalised_dwell_ns":weighted/C/incident*1e9 if incident else None,
        "entered_normalised_dwell_ns":weighted/C/entered*1e9 if entered else None,
        "circulating_path_proxy_Wm":angular_weighted,
        "pending_power_W":pending, "terminal_statuses":statuses,
        "wall_torque_Nm":data["metrics"]["wall_torque_Nm"],
        "target_W":data["metrics"]["target_W"],
        "model_status": "ray-path proxy; not wave-optical WGM or Q",
    }

if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("events", nargs="+")
    parser.add_argument("--output")
    options=parser.parse_args()
    rows=[]
    for filename in options.events:
        with open(filename,encoding="utf-8") as stream:
            content=json.load(stream)
        row=analyse(content.get("events",content))
        row["filename"]=filename
        rows.append(row)
    result=json.dumps({"schema":"kozyrev-confinement-proxy/1","results":rows},indent=2)
    if options.output:
        with open(options.output,"w",encoding="utf-8") as target:
            target.write(result+"\n")
    else:
        print(result)
