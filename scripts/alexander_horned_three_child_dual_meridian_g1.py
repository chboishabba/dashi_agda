#!/usr/bin/env python3
"""Exact rational tame 3D G1 model: planar genus-3 spine + dual loops.

Vertices and edges define three disjoint planar triangle cycles meeting
only at O. A sufficiently small PL regular neighbourhood of the graph
is a genus-three handlebody. Each meridian is a vertical polygonal
rectangle with one positive transverse intersection with its OWN
planar triangle disk and no intersections with the other two disks.

The exact linking matrix (after orienting meridian loops) is I_3.
This certifies a labelled DUAL LOOP chart in the tame handlebody
EXTERIOR. It does not prove the selected WILD three-child inclusion,
ambient slide homeomorphism, or nested limit.
"""
from fractions import Fraction as F
from itertools import combinations

O=(F(0),F(0))
faces={
  'a':((F(8),F(1)),(F(8),F(-1))),
  'b':((F(-5),F(8)),(F(-6),F(7))),
  'c':((F(-5),F(-8)),(F(-6),F(-7))),
}
# Each meridian rectangle is in a vertical plane whose two z-axis
# crossings project to one point inside its own disk and one outside.
crossings={
  'a':((F(6),F(0)),(F(9),F(0))),
  'b':((F(-4),F(5)),(F(-8),F(10))),
  'c':((F(-4),F(-5)),(F(-8),F(-10))),
}
def det(a,b,c):
 return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def strictly_inside(x,tri):
 p,q=tri
 signs=(det(O,p,x),det(p,q,x),det(q,O,x))
 return all(t>0 for t in signs) or all(t<0 for t in signs)
def on_segment(x,a,b):
 return det(a,b,x)==0 and all(min(a[j],b[j])<=x[j]<=max(a[j],b[j]) for j in range(2))
def audit():
  labels=tuple(faces)
  graph_edges=[]
  vertices={O}
  for label,(p,q) in faces.items():
    vertices.update((p,q))
    graph_edges.extend(((label,O,p),(label,p,q),(label,q,O)))
  assert len(vertices)==7 and len(graph_edges)==9
  assert len(graph_edges)-len(vertices)+1==3
  linking=[]
  for meridian in labels:
    inside,outside=crossings[meridian]
    # Rectangular meridian has vertices (inside,-2),(inside,+2),
    # (outside,+2),(outside,-2) and closes at the initial vertex.
    # It crosses the horizontal plane at exactly those two points.
    assert inside!=outside
    assert all(not on_segment(t,a,b) for t in (inside,outside)
               for _,a,b in graph_edges)
    row=[]
    for disk in labels:
      assert not strictly_inside(outside,faces[disk])
      sgn=1 if det(O,*faces[disk])>0 else -1
      row.append(sgn if strictly_inside(inside,faces[disk]) else 0)
    linking.append(row)
  # Orient each meridian according to the chosen disk normal.
  oriented=[[linking[i][j]*linking[i][i] for j in range(3)]
            for i in range(3)]
  assert oriented==[[1,0,0],[0,1,0],[0,0,1]]
  print("PASS rational 7-vertex/9-edge planar rank-three graph")
  print("PASS all six z-axis crossing projections avoid graph edges")
  print("PASS three meridian polygonal rectangles each pierce one disk")
  print("PASS oriented linking matrix:",oriented)
  print("BOUNDARY: tame complement linking chart is not Hatcher ternary stage inclusion")
  print("BOUNDARY: no cap-relative homeomorphism or wild limit supplied")
if __name__=="__main__":audit()
