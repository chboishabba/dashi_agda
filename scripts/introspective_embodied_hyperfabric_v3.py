#!/usr/bin/env python3
"""Introspective embodied hyperfabric v3.

Theory -> deterministic raster -> pixel-only observer -> symmetry/gate receipt.

After rendering, the observer does not read THEORY.  It recovers:
  * supervoxel boxes and fibre occupancy,
  * incidence corridors,
  * sampled vector fields encoded as square origins + circular heads,
  * finite divergence/curl/chirality proxies from recovered vectors,
  * orientation/polarization line angle,
  * embodied gate fill state.
"""
from pathlib import Path
import json, math
import cv2
import numpy as np

OUT = Path("artifacts/introspective-embodied-hyperfabric-v3")
OUT.mkdir(parents=True, exist_ok=True)
W, H = 1400, 900
THEORY = {
    "hierarchy": ["fibre", "cubie", "supervoxel", "hyperfabric"],
    "supervoxels": {
        "S0": {"rect": [100,100,400,250], "fibres": 3, "mode": "none"},
        "S1": {"rect": [900,100,400,250], "fibres": 1, "mode": "source", "gate": "open"},
        "S2": {"rect": [100,550,400,250], "fibres": 2, "mode": "rotation", "gate": "closed"},
        "S3": {"rect": [900,550,400,250], "fibres": 3, "mode": "none"},
    },
    "edges": [["S0","S1"],["S0","S2"],["S1","S3"],["S2","S3"]],
    "intent": "same boundaries, symmetry-distinct intermediate routes, body-indexed gate split",
}
(OUT / "theory.json").write_text(json.dumps(THEORY, indent=2))
img = np.full((H, W, 3), 255, np.uint8)
boxes = [tuple(THEORY["supervoxels"][f"S{i}"]["rect"]) for i in range(4)]
for a,b in [((500,225),(900,225)),((300,350),(300,550)),
            ((1100,350),(1100,550)),((500,675),(900,675))]:
    cv2.line(img, a, b, (130,130,130), 20)
for i,(x,y,w,h) in enumerate(boxes):
    cv2.rectangle(img,(x,y),(x+w,y+h),(0,0,0),5)
    n = THEORY["supervoxels"][f"S{i}"]["fibres"]
    for k in range(n):
        fx = int(x + w*(k+1)/(n+1)); fy = y+48
        cv2.circle(img,(fx,fy),18,(64,64,64),-1)
        cv2.circle(img,(fx,fy),18,(0,0,0),2)

def draw_vector_samples(rect, kind):
    x,y,w,h = rect
    cx,cy = x+w//2, y+165
    origins=[(-45,0),(45,0),(0,-45),(0,45)]
    if kind == "source":
        vectors=[(-25,0),(25,0),(0,-25),(0,25)]
        orientation_angle=0.0; gate_filled=False
    else:
        vectors=[(0,-25),(0,25),(25,0),(-25,0)]
        orientation_angle=math.pi/4; gate_filled=True
    for (ox,oy),(vx,vy) in zip(origins,vectors):
        p=(cx+ox,cy+oy); q=(p[0]+vx,p[1]+vy)
        cv2.rectangle(img,(p[0]-6,p[1]-6),(p[0]+6,p[1]+6),(0,0,0),2)
        cv2.circle(img,q,5,(0,0,0),-1)
    ocx,ocy=x+320,y+150
    dx=int(round(28*math.cos(orientation_angle)))
    dy=int(round(28*math.sin(orientation_angle)))
    cv2.line(img,(ocx-dx,ocy-dy),(ocx+dx,ocy+dy),(0,0,0),4)
    gx,gy=x+340,y+210
    cv2.rectangle(img,(gx-10,gy-10),(gx+10,gy+10),(0,0,0),-1 if gate_filled else 2)

draw_vector_samples(boxes[1], "source")
draw_vector_samples(boxes[2], "rotation")
png=OUT/"embodied_hyperfabric_v3.png"
cv2.imwrite(str(png),img)

# ------------------------ PIXEL-ONLY OBSERVER ------------------------
observed=cv2.imread(str(png)); gray=cv2.cvtColor(observed,cv2.COLOR_BGR2GRAY)
black=cv2.inRange(gray,0,20)
contours,_=cv2.findContours(black,cv2.RETR_LIST,cv2.CHAIN_APPROX_SIMPLE)
rects=[]
for c in contours:
    x,y,w,h=cv2.boundingRect(c)
    if 380<=w<=420 and 230<=h<=270:
        if not any(abs(x-r[0])<10 and abs(y-r[1])<10 for r in rects):
            rects.append((x,y,w,h))
rects.sort(key=lambda r:(r[1],r[0]))

fmask=cv2.inRange(gray,45,85)
n,labels,stats,cents=cv2.connectedComponentsWithStats(fmask,8)
fibres=[]
for i in range(1,n):
    x,y,w,h,area=stats[i]
    if 800<=area<=1400 and 30<=w<=50 and 30<=h<=50:
        fibres.append((float(cents[i][0]),float(cents[i][1])))
fibre_counts=[sum(x<fx<x+w and y<fy<y+h for fx,fy in fibres) for x,y,w,h in rects]

def gray_fraction(x1,y1,x2,y2):
    roi=gray[y1:y2,x1:x2]
    return 0.0 if roi.size==0 else float(np.mean((roi>=100)&(roi<=150)))
edges=[]
for i,a in enumerate(rects):
    ax,ay,aw,ah=a; acx,acy=ax+aw/2,ay+ah/2
    for j,b in enumerate(rects[i+1:],start=i+1):
        bx,by,bw,bh=b; bcx,bcy=bx+bw/2,by+bh/2; support=0.0
        if abs(acy-bcy)<30:
            left,right=sorted([a,b],key=lambda r:r[0])
            support=gray_fraction(left[0]+left[2],int((acy+bcy)/2)-15,right[0],int((acy+bcy)/2)+15)
        elif abs(acx-bcx)<30:
            top,bottom=sorted([a,b],key=lambda r:r[1])
            support=gray_fraction(int((acx+bcx)/2)-15,top[1]+top[3],int((acx+bcx)/2)+15,bottom[1])
        if support>.25: edges.append((i,j))

def recover_vectors(rect):
    x,y,w,h=rect
    roi=gray[y+90:y+235,x+90:x+285]
    th=cv2.threshold(roi,30,255,cv2.THRESH_BINARY_INV)[1]
    cs,_=cv2.findContours(th,cv2.RETR_EXTERNAL,cv2.CHAIN_APPROX_SIMPLE)
    origins=[]; heads=[]
    for c in cs:
        area=cv2.contourArea(c)
        M=cv2.moments(c)
        if M["m00"]==0: continue
        p=np.array([M["m10"]/M["m00"]+x+90, M["m01"]/M["m00"]+y+90])
        if 170<=area<=230: origins.append(p)
        elif 40<=area<=90: heads.append(p)
    vectors=[]; remaining=heads[:]
    for o in origins:
        if not remaining: continue
        k=min(range(len(remaining)),key=lambda i:np.linalg.norm(remaining[i]-o))
        hpt=remaining.pop(k)
        if np.linalg.norm(hpt-o)<=40: vectors.append((o,hpt-o))
    return vectors

def geometry_proxies(rect):
    vectors=recover_vectors(rect)
    x,y,w,h=rect; center=np.array([x+w/2,y+165.0])
    div=0.0; curl=0.0
    for origin,v in vectors:
        r=origin-center; nr=np.linalg.norm(r); nv=np.linalg.norm(v)
        if nr<1 or nv<1: continue
        ru=r/nr; vu=v/nv
        div += float(np.dot(ru,vu))
        curl += float(ru[0]*vu[1]-ru[1]*vu[0])
    return vectors,div,curl

def orientation_angle(rect):
    x,y,w,h=rect; roi=gray[y+110:y+190,x+285:x+355]
    e=cv2.Canny(roi,50,150)
    ls=cv2.HoughLinesP(e,1,np.pi/180,20,minLineLength=30,maxLineGap=8)
    angles=[]
    if ls is not None:
        # OpenCV versions return either (N,1,4) or (N,4); normalize both.
        for x1,y1,x2,y2 in np.asarray(ls).reshape(-1,4):
            angles.append(math.degrees(math.atan2(int(y2)-int(y1),int(x2)-int(x1))))
    return None if not angles else float(np.median(angles))

def gate_fill(rect):
    x,y,w,h=rect; roi=gray[y+195:y+226,x+325:x+356]
    return float(np.mean(roi<40))

mode_observations=[]
for idx in [1,2]:
    vectors,div,curl=geometry_proxies(rects[idx]); angle=orientation_angle(rects[idx]); fill=gate_fill(rects[idx])
    mode_observations.append({
        "box":idx,
        "recovered_vector_count":len(vectors),
        "divergence_proxy":round(div,3),
        "curl_proxy":round(curl,3),
        "chirality":"positive" if curl>.5 else ("negative" if curl<-.5 else "neutral"),
        "orientation_angle_deg":None if angle is None else round(angle,1),
        "gate_fill_ratio":round(fill,3),
        "gate_class":"closed-filled" if fill>.35 else "open-outline",
    })
receipt={
    "observer_boundary":"pixels only after render; THEORY not read",
    "observed_supervoxel_count":len(rects),
    "observed_fibres_per_supervoxel":fibre_counts,
    "observed_edges":[list(e) for e in edges],
    "mode_observations":mode_observations,
    "source_like_route_recovered":any(m["divergence_proxy"]>2.5 and abs(m["curl_proxy"])<1 for m in mode_observations),
    "rotational_route_recovered":any(abs(m["divergence_proxy"])<1 and abs(m["curl_proxy"])>2.5 for m in mode_observations),
    "biology_inferred_from_pixels":False,
    "phenomenal_consciousness_inferred_from_pixels":False,
}
(OUT/"opencv_symmetry_observations.json").write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
