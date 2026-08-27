#!/usr/bin/env python3
"""Render a finite embodied hyperfabric patch, recover structure from pixels,
and write an observation receipt.  The CV stage intentionally does not read
or import the theory metadata used by the renderer.
"""
from pathlib import Path
import json
import cv2
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, Circle, FancyArrowPatch

OUT = Path("artifacts/introspective-embodied-hyperfabric")
OUT.mkdir(parents=True, exist_ok=True)

SUPERVOXELS = [
    ("S0", "broad / regulated",      (80,120,620,330), [(220,250),(390,250),(560,250)]),
    ("S1", "contracted / mobilised", (900,120,620,330), [(1210,250)]),
    ("S2", "reopened / activated",   (80,570,620,330), [(300,700),(500,700)]),
    ("S3", "goal-compatible future", (900,570,620,330), [(1040,700),(1210,700),(1380,700)]),
]

# Stage 1: theory receipt used only by renderer.
theory = {
    "hierarchy": ["fibre", "cubie", "supervoxel", "hyperfabric"],
    "supervoxels": [
        {"id": sid, "label": label, "rect": list(rect), "fibres": [list(p) for p in fibres]}
        for sid, label, rect, fibres in SUPERVOXELS
    ],
}
(OUT / "theory.json").write_text(json.dumps(theory, indent=2))

# Stage 2: deterministic visualization.
fig, ax = plt.subplots(figsize=(16,10), dpi=100)
ax.set_xlim(0,1600); ax.set_ylim(1000,0); ax.axis("off")
for sid,label,(x,y,w,h),fibres in SUPERVOXELS:
    ax.add_patch(Rectangle((x,y),w,h,fill=False,linewidth=4))
    ax.add_patch(Rectangle((x+70,y+80),w-140,h-150,fill=False,linewidth=2,linestyle="--"))
    ax.text(x+15,y+28,f"{sid}: {label}",fontsize=15,va="top")
    for fx,fy in fibres:
        ax.add_patch(Circle((fx,fy),28,facecolor="0.25",edgecolor="black",linewidth=2))
for p0,p1 in [((700,285),(900,285)),((1210,450),(1210,570)),((700,735),(900,735))]:
    ax.add_patch(FancyArrowPatch(p0,p1,arrowstyle="->",mutation_scale=18,linewidth=2))
ax.add_patch(FancyArrowPatch((620,410),(980,650),arrowstyle="->",mutation_scale=18,linewidth=2,linestyle=":"))
png = OUT / "embodied_hyperfabric.png"
fig.savefig(png, dpi=100)
plt.close(fig)

# Stage 3: CV-only recovery from pixels.
img = cv2.imread(str(png))
gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
mask = cv2.inRange(gray,45,90)
n, labels, stats, cents = cv2.connectedComponentsWithStats(mask,8)
fibres=[]
for i in range(1,n):
    x,y,w,h,area = stats[i]
    if 900 <= area <= 1500 and 30 <= w <= 50 and 30 <= h <= 50:
        fibres.append((float(cents[i][0]),float(cents[i][1]),int(area)))

edges = cv2.Canny(gray,50,150,apertureSize=3)
lines = cv2.HoughLinesP(edges,1,np.pi/180,threshold=140,minLineLength=180,maxLineGap=20)
outer_h=[]; outer_v=[]
for x1,y1,x2,y2 in ([] if lines is None else lines[:,0]):
    if abs(y2-y1)<=3 and abs(x2-x1)>=450: outer_h.append((x1,y1,x2,y2))
    if abs(x2-x1)<=3 and abs(y2-y1)>=230: outer_v.append((x1,y1,x2,y2))

def cluster(vals,tol=7):
    vals=sorted(int(v) for v in vals); groups=[]
    for v in vals:
        if not groups or abs(v-np.mean(groups[-1]))>tol: groups.append([v])
        else: groups[-1].append(v)
    return [int(round(np.mean(g))) for g in groups]

xs=cluster([x1 for x1,_,x2,_ in outer_v]+[x2 for x1,_,x2,_ in outer_v])
ys=cluster([y1 for _,y1,_,y2 in outer_h]+[y2 for _,y1,_,y2 in outer_h])
rects=[]
for xa in xs:
    for xb in xs:
        if 460 <= xb-xa <= 500:
            for ya in ys:
                for yb in ys:
                    if 240 <= yb-ya <= 270:
                        r=(xa,ya,xb-xa,yb-ya)
                        if not any(abs(xa-q[0])<10 and abs(ya-q[1])<10 for q in rects): rects.append(r)
rects.sort(key=lambda r:(r[1],r[0]))
fibres.sort(key=lambda q:(q[1],q[0]))
counts=[sum(1 for cx,cy,_ in fibres if x<cx<x+w and y<cy<y+h) for x,y,w,h in rects]

obs={
    "observed_supervoxel_count": len(rects),
    "observed_fibre_count": len(fibres),
    "observed_fibres_per_supervoxel": counts,
    "observed_nonuniform_fibre_occupancy": len(set(counts)) > 1,
    "detector_input_boundary": "pixels only; theory metadata not supplied to CV stage",
}
(OUT / "opencv_observations.json").write_text(json.dumps(obs,indent=2))
print(json.dumps(obs,indent=2))
