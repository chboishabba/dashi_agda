#!/usr/bin/env python3
"""Deterministic Aristotle introspective round trip.

Pipeline:
  finite Aristotle specimen -> typed SVG -> PNG -> OpenCV decode -> JSON

The decoder reads geometry from pixels.  It does not parse labels or Agda.
The final assertions require exact recovery of:
  * six states and seven actions;
  * proved/unproved status;
  * action source and target lists;
  * the nontrivial observer fibre {S1, S1p}.

Visual grammar after two introspective refinements:
  circle             = state
  wide rectangle     = action
  double outline     = proved
  triangle tag       = member of the shared nontrivial observer fibre
  thick incidence    = action source
  thin incidence     = action target

An intermediate node occludes a candidate long edge.  This prevents a real
short edge from being mistaken for the tail of a collinear long edge.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import cairosvg
import cv2
import numpy as np

STATES = {
    "S0":  {"xy": (120, 450), "proved": True,  "fibre": "root"},
    "S1":  {"xy": (440, 150), "proved": True,  "fibre": "q1"},
    "S1p": {"xy": (440, 290), "proved": True,  "fibre": "q1"},
    "S2":  {"xy": (440, 450), "proved": True,  "fibre": "q2"},
    "S3":  {"xy": (440, 620), "proved": True,  "fibre": "q3"},
    "S4":  {"xy": (440, 790), "proved": False, "fibre": "q4"},
}

ACTIONS = {
    "A0":  {"xy": (275, 330), "proved": True,  "source": "S0",  "targets": ["S1", "S2"]},
    "A1":  {"xy": (275, 560), "proved": True,  "source": "S0",  "targets": ["S3"]},
    "A2":  {"xy": (275, 730), "proved": False, "source": "S0",  "targets": ["S4"]},
    "T1":  {"xy": (720, 150), "proved": True,  "source": "S1",  "targets": []},
    "T1p": {"xy": (720, 290), "proved": True,  "source": "S1p", "targets": []},
    "T2":  {"xy": (720, 450), "proved": True,  "source": "S2",  "targets": []},
    "T3":  {"xy": (720, 620), "proved": True,  "source": "S3",  "targets": []},
}


def line(a, b, width):
    return (
        f'<line x1="{a[0]}" y1="{a[1]}" x2="{b[0]}" y2="{b[1]}" '
        f'stroke="black" stroke-width="{width}"/>'
    )


def circle(xy, radius):
    return (
        f'<circle cx="{xy[0]}" cy="{xy[1]}" r="{radius}" '
        'fill="white" stroke="black" stroke-width="4"/>'
    )


def rect_center(xy, width, height):
    x, y = xy
    return (
        f'<rect x="{x-width/2}" y="{y-height/2}" width="{width}" height="{height}" '
        'fill="white" stroke="black" stroke-width="4"/>'
    )


def triangle_tag(xy):
    x, y = xy
    return f'<polygon points="{x+43},{y-29} {x+55},{y-29} {x+49},{y-41}" fill="black"/>'


def render_svg() -> str:
    svg = [
        '<svg xmlns="http://www.w3.org/2000/svg" width="1000" height="900" viewBox="0 0 1000 900">',
        '<rect width="1000" height="900" fill="white"/>',
    ]
    for action in ACTIONS.values():
        svg.append(line(STATES[action["source"]]["xy"], action["xy"], 8))
        for target in action["targets"]:
            svg.append(line(action["xy"], STATES[target]["xy"], 3))

    for state_id, state in STATES.items():
        svg.append(circle(state["xy"], 34))
        if state["proved"]:
            svg.append(circle(state["xy"], 25))
        if state["fibre"] == "q1":
            svg.append(triangle_tag(state["xy"]))
        x, y = state["xy"]
        svg.append(
            f'<text x="{x}" y="{y+5}" font-family="monospace" font-size="18" '
            f'text-anchor="middle">{state_id}</text>'
        )

    for action_id, action in ACTIONS.items():
        svg.append(rect_center(action["xy"], 84, 52))
        if action["proved"]:
            svg.append(rect_center(action["xy"], 66, 34))
        x, y = action["xy"]
        svg.append(
            f'<text x="{x}" y="{y+5}" font-family="monospace" font-size="17" '
            f'text-anchor="middle">{action_id}</text>'
        )

    legend = [
        "triangle tag = shared observer fibre",
        "double outline = proved",
        "circle = state",
        "wide rectangle = action",
        "thick edge = source incidence",
        "thin edge = target incidence",
    ]
    for i, text in enumerate(legend):
        svg.append(
            f'<text x="590" y="{704 + 28*i}" font-family="sans-serif" font-size="18">{text}</text>'
        )
    svg.append("</svg>")
    return "\n".join(svg)


def dedupe_rectangles(rects):
    out = []
    for candidate in sorted(rects):
        if not any(abs(candidate[0]-old[0]) < 8 and abs(candidate[1]-old[1]) < 8 for old in out):
            out.append(candidate)
    return out


def point_segment_distance(point, a, b):
    px, py = point
    ax, ay = a
    bx, by = b
    vx, vy = bx-ax, by-ay
    wx, wy = px-ax, py-ay
    vv = vx*vx + vy*vy
    if vv == 0:
        return math.hypot(px-ax, py-ay), 0.0
    t = max(0.0, min(1.0, (wx*vx + wy*vy) / vv))
    qx, qy = ax + t*vx, ay + t*vy
    return math.hypot(px-qx, py-qy), t


def decode_png(png_path: Path):
    img = cv2.imread(str(png_path), cv2.IMREAD_GRAYSCALE)
    if img is None:
        raise RuntimeError(f"could not read {png_path}")
    graph = img[:, :820]
    bw = cv2.threshold(graph, 180, 255, cv2.THRESH_BINARY_INV)[1]

    circles = cv2.HoughCircles(
        graph, cv2.HOUGH_GRADIENT, dp=1.2, minDist=70,
        param1=120, param2=34, minRadius=28, maxRadius=39,
    )
    if circles is None:
        raise AssertionError("no state circles recovered")
    state_centers = [
        tuple(map(int, row))
        for row in np.round(circles[0]).astype(int)
        if row[0] < 520
    ]

    contours, _ = cv2.findContours(bw, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
    rectangles = []
    triangles = []
    for contour in contours:
        x, y, w, h = cv2.boundingRect(contour)
        area = cv2.contourArea(contour)
        perimeter = cv2.arcLength(contour, True)
        approx = cv2.approxPolyDP(contour, 0.04 * perimeter, True) if perimeter else []
        ratio = w / h if h else 0
        if 76 <= w <= 92 and 45 <= h <= 60 and 1.35 <= ratio <= 1.95 and area > 2500:
            rectangles.append((x+w//2, y+h//2, w, h))
        if len(approx) == 3 and 8 <= w <= 18 and 8 <= h <= 18 and area >= 35:
            triangles.append((x+w//2, y+h//2))
    action_centers = dedupe_rectangles(rectangles)

    root_state = min(state_centers, key=lambda z: z[0])
    other_states = sorted([z for z in state_centers if z != root_state], key=lambda z: z[1])
    state_named = {"S0": root_state}
    for name, center in zip(["S1", "S1p", "S2", "S3", "S4"], other_states):
        state_named[name] = center

    left_actions = sorted([z for z in action_centers if z[0] < 500], key=lambda z: z[1])
    right_actions = sorted([z for z in action_centers if z[0] >= 500], key=lambda z: z[1])
    action_named = {}
    for name, center in zip(["A0", "A1", "A2"], left_actions):
        action_named[name] = center
    for name, center in zip(["T1", "T1p", "T2", "T3"], right_actions):
        action_named[name] = center

    def ring_density(cx, cy, radius):
        mask = np.zeros_like(bw)
        cv2.circle(mask, (cx, cy), radius, 255, 2)
        values = bw[mask > 0]
        return float((values > 0).mean())

    def rect_inner_density(cx, cy, hw=33, hh=17):
        points = [(x, cy-hh) for x in range(cx-hw, cx+hw+1)]
        points += [(x, cy+hh) for x in range(cx-hw, cx+hw+1)]
        points += [(cx-hw, y) for y in range(cy-hh, cy+hh+1)]
        points += [(cx+hw, y) for y in range(cy-hh, cy+hh+1)]
        values = []
        for x, y in points:
            patch = bw[max(0, y-2):y+3, max(0, x-2):x+3]
            if patch.size:
                values.append((patch > 0).mean())
        return float(np.mean(values))

    all_centers = {
        **{name: (z[0], z[1]) for name, z in state_named.items()},
        **{name: (z[0], z[1]) for name, z in action_named.items()},
    }

    def blocked(p, q, endpoint_names):
        for name, center in all_centers.items():
            if name in endpoint_names:
                continue
            distance, t = point_segment_distance(center, p, q)
            if 0.12 < t < 0.88 and distance < 42:
                return True
        return False

    def segment_density(p, q, width=11, state_margin=43, action_margin=52):
        x1, y1 = p
        x2, y2 = q
        vx, vy = x2-x1, y2-y1
        length = math.hypot(vx, vy)
        ux, uy = vx/length, vy/length
        a = (int(round(x1 + ux*state_margin)), int(round(y1 + uy*state_margin)))
        b = (int(round(x2 - ux*action_margin)), int(round(y2 - uy*action_margin)))
        mask = np.zeros_like(bw)
        cv2.line(mask, a, b, 255, width)
        values = bw[mask > 0]
        return float((values > 0).mean()) if values.size else 0.0

    state_proved = {
        name: ring_density(center[0], center[1], 25) > 0.35
        for name, center in state_named.items()
    }
    action_proved = {
        name: rect_inner_density(center[0], center[1]) > 0.28
        for name, center in action_named.items()
    }

    edge_roles = {}
    segment_densities = {}
    for state_name, (sx, sy, _) in state_named.items():
        for action_name, (ax, ay, _, _) in action_named.items():
            key = f"{state_name}-{action_name}"
            if blocked((sx, sy), (ax, ay), {state_name, action_name}):
                density = 0.0
                role = "absent"
            else:
                density = segment_density((sx, sy), (ax, ay))
                role = "source" if density > 0.58 else ("target" if density > 0.18 else "absent")
            segment_densities[key] = round(density, 3)
            edge_roles[key] = role

    sources = {}
    targets = {name: [] for name in action_named}
    for key, role in edge_roles.items():
        state_name, action_name = key.split("-")
        if role == "source":
            sources[action_name] = state_name
        elif role == "target":
            targets[action_name].append(state_name)
    for action_name in targets:
        targets[action_name].sort()

    tagged = []
    for tx, ty in triangles:
        state_name, center = min(
            state_named.items(),
            key=lambda kv: math.hypot(kv[1][0]-tx, kv[1][1]-ty),
        )
        if math.hypot(center[0]-tx, center[1]-ty) < 80:
            tagged.append(state_name)
    tagged = sorted(set(tagged))

    return {
        "state_count": len(state_named),
        "action_count": len(action_named),
        "states": {name: {"proved": bool(state_proved[name])} for name in state_named},
        "actions": {
            name: {
                "proved": bool(action_proved[name]),
                "source": sources.get(name),
                "targets": targets[name],
            }
            for name in action_named
        },
        "shared_fibre_tagged_states": tagged,
        "edge_roles": edge_roles,
        "segment_densities": segment_densities,
    }


def assert_exact(decoded):
    expected_states = {
        "S0": {"proved": True}, "S1": {"proved": True}, "S1p": {"proved": True},
        "S2": {"proved": True}, "S3": {"proved": True}, "S4": {"proved": False},
    }
    expected_actions = {
        name: {"proved": action["proved"], "source": action["source"], "targets": action["targets"]}
        for name, action in ACTIONS.items()
    }
    assert decoded["state_count"] == 6
    assert decoded["action_count"] == 7
    assert decoded["states"] == expected_states
    assert decoded["actions"] == expected_actions
    assert decoded["shared_fibre_tagged_states"] == ["S1", "S1p"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--out",
        type=Path,
        default=Path("artifacts/introspection/aristotle"),
        help="artifact directory",
    )
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)

    svg = render_svg()
    svg_path = args.out / "aristotle_mcgshypergraph_faithful.svg"
    png_path = args.out / "aristotle_mcgshypergraph_faithful.png"
    json_path = args.out / "opencv_decode_faithful.json"

    svg_path.write_text(svg, encoding="utf-8")
    cairosvg.svg2png(bytestring=svg.encode("utf-8"), write_to=str(png_path))
    decoded = decode_png(png_path)
    assert_exact(decoded)
    json_path.write_text(json.dumps(decoded, indent=2) + "\n", encoding="utf-8")
    print("ROUNDTRIP_OK")
    print(json.dumps(decoded, indent=2))


if __name__ == "__main__":
    main()
