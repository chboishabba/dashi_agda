#!/usr/bin/env python3
"""Introspective hyperfabric v2.

Pipeline:
  finite theory -> deterministic pixel visualization -> CV-only observer
  -> machine-readable incidence/path receipt.

The observer stage does not read THEORY, box labels, intended fibre counts or
intended graph edges. It infers large supervoxel rectangles, compact fibre
components, corridor incidence and two-step paths from pixels only.
"""
from pathlib import Path
import json
import cv2
import numpy as np

OUT = Path("artifacts/introspective-embodied-hyperfabric-v2")
OUT.mkdir(parents=True, exist_ok=True)

WIDTH, HEIGHT = 1400, 900

THEORY = {
    "hierarchy": ["fibre", "cubie", "supervoxel", "hyperfabric"],
    "supervoxels": {
        "S0": {"rect": [100, 100, 400, 250], "fibres": [[200,230],[300,230],[400,230]]},
        "S1": {"rect": [900, 100, 400, 250], "fibres": [[1100,230]]},
        "S2": {"rect": [100, 550, 400, 250], "fibres": [[250,680],[350,680]]},
        "S3": {"rect": [900, 550, 400, 250], "fibres": [[1000,680],[1100,680],[1200,680]]},
    },
    "edges": [["S0","S1"],["S0","S2"],["S1","S3"],["S2","S3"]],
    "two_boundary_intent": "two distinct intermediate routes S0 -> {S1,S2} -> S3",
}
(OUT / "theory.json").write_text(json.dumps(THEORY, indent=2))

# -------------------- stage 2: deterministic visualization --------------------
img = np.full((HEIGHT, WIDTH, 3), 255, np.uint8)
corridor = (120, 120, 120)

# Draw incidence corridors first.
cv2.rectangle(img, (500,215), (900,235), corridor, -1)
cv2.rectangle(img, (290,350), (310,550), corridor, -1)
cv2.rectangle(img, (1090,350), (1110,550), corridor, -1)
cv2.rectangle(img, (500,665), (900,685), corridor, -1)

for sid, payload in THEORY["supervoxels"].items():
    x, y, w, h = payload["rect"]
    cv2.rectangle(img, (x,y), (x+w,y+h), (0,0,0), 5)

    # Dashed inner rectangle denotes one cubie-local face.
    ix, iy, iw, ih = x+60, y+70, w-120, h-110
    for xx in range(ix, ix+iw, 30):
        cv2.line(img, (xx,iy), (min(xx+15,ix+iw),iy), (0,0,0), 2)
        cv2.line(img, (xx,iy+ih), (min(xx+15,ix+iw),iy+ih), (0,0,0), 2)
    for yy in range(iy, iy+ih, 30):
        cv2.line(img, (ix,yy), (ix,min(yy+15,iy+ih)), (0,0,0), 2)
        cv2.line(img, (ix+iw,yy), (ix+iw,min(yy+15,iy+ih)), (0,0,0), 2)

    cv2.putText(img, sid, (x+15,y+35), cv2.FONT_HERSHEY_SIMPLEX,
                1.0, (0,0,0), 2, cv2.LINE_AA)
    for fx, fy in payload["fibres"]:
        cv2.circle(img, (fx,fy), 28, (64,64,64), -1)
        cv2.circle(img, (fx,fy), 28, (0,0,0), 2)

png = OUT / "embodied_hyperfabric_v2.png"
cv2.imwrite(str(png), img)

# -------------------- stage 3: CV-only observation --------------------
# From here on, THEORY is intentionally not accessed.
observed = cv2.imread(str(png))
gray = cv2.cvtColor(observed, cv2.COLOR_BGR2GRAY)

# Compact mid-gray connected components are fibre candidates.
fibre_mask = cv2.inRange(gray, 45, 85)
n, labels, stats, cents = cv2.connectedComponentsWithStats(fibre_mask, 8)
fibres = []
for i in range(1, n):
    x, y, w, h, area = stats[i]
    if 1800 <= area <= 2800 and 45 <= w <= 65 and 45 <= h <= 65:
        fibres.append((float(cents[i][0]), float(cents[i][1])))
fibres.sort(key=lambda p: (p[1], p[0]))

# Large near-black rectangular contours are supervoxel candidates.
black = cv2.inRange(gray, 0, 20)
contours, _ = cv2.findContours(black, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
rects = []
for contour in contours:
    x, y, w, h = cv2.boundingRect(contour)
    if 380 <= w <= 420 and 230 <= h <= 270:
        if not any(abs(x-r[0]) < 10 and abs(y-r[1]) < 10 for r in rects):
            rects.append((x,y,w,h))
rects.sort(key=lambda r: (r[1], r[0]))

fibre_counts = []
for x,y,w,h in rects:
    fibre_counts.append(sum(x < fx < x+w and y < fy < y+h for fx,fy in fibres))

# Corridor recovery uses only geometric alignment and gray-pixel support in the gap.
def gray_fraction(x1, y1, x2, y2):
    roi = gray[y1:y2, x1:x2]
    if roi.size == 0:
        return 0.0
    return float(np.mean((roi >= 100) & (roi <= 140)))

edges = []
for i, left in enumerate(rects):
    lx,ly,lw,lh = left
    lcx,lcy = lx+lw/2, ly+lh/2
    for j, right in enumerate(rects[i+1:], start=i+1):
        rx,ry,rw,rh = right
        rcx,rcy = rx+rw/2, ry+rh/2
        support = 0.0

        if abs(lcy-rcy) < 30:
            a,b = sorted([left,right], key=lambda r:r[0])
            support = gray_fraction(a[0]+a[2], int((lcy+rcy)/2)-15,
                                    b[0], int((lcy+rcy)/2)+15)
        elif abs(lcx-rcx) < 30:
            a,b = sorted([left,right], key=lambda r:r[1])
            support = gray_fraction(int((lcx+rcx)/2)-15, a[1]+a[3],
                                    int((lcx+rcx)/2)+15, b[1])

        if support > 0.25:
            edges.append((i,j))

adj = {i:set() for i in range(len(rects))}
for i,j in edges:
    adj[i].add(j)
    adj[j].add(i)

length2 = []
if 0 in adj and 3 in adj:
    for mid in sorted(adj[0]):
        if 3 in adj[mid]:
            length2.append([0,mid,3])

receipt = {
    "observer_boundary": "pixels only after render; theory metadata not read",
    "observed_supervoxel_count": len(rects),
    "observed_fibre_count": len(fibres),
    "observed_fibres_per_supervoxel": fibre_counts,
    "observed_edges": [list(edge) for edge in edges],
    "observed_degree_profile": [len(adj[i]) for i in sorted(adj)],
    "observed_length2_paths_0_to_3": length2,
    "two_distinct_intermediate_paths": len(length2) >= 2,
    "biological_mechanism_inferred_from_pixels": False,
    "clinical_meaning_inferred_from_pixels": False,
}
(OUT / "opencv_incidence_observations.json").write_text(json.dumps(receipt, indent=2))
print(json.dumps(receipt, indent=2))
