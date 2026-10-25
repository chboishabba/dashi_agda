#!/usr/bin/env python3
r"""Exact rational inequalities for an actual open cover of a horned-C3 exterior.

For any E subset R^3 with the subspace topology:
 C=E ∩ intersection_i {distance(x,c_i)>r_inner};
 S_i=E ∩ {distance(x,c_i)<r_outer}; U_i=C union S_i.
All are relatively open. Coverage follows from r_inner < r_outer;
pairwise disjoint S_i follow from centre separation > 2*r_outer.
The wild infinite geometry, central pi1, and satellite homotopies are
NOT certified by these finite algebraic inequalities.
"""
from fractions import Fraction as Q
from itertools import combinations
import json

RIN=Q(15,4)
ROUT=Q(17,4)
SAT=Q(1)
TUBE=Q(1,4)
CENTRES=((Q(9),Q(0),Q(0)),(Q(0),Q(9),Q(0)),(Q(0),Q(0),Q(9)))

def d2(x,y):
    return sum((a-b)**2 for a,b in zip(x,y))

def exact_certificate():
    pair_dist2=[d2(CENTRES[i],CENTRES[j]) for i,j in combinations(range(3),2)]
    assert pair_dist2==[Q(162)]*3
    assert (2*ROUT)**2<min(pair_dist2)
    assert Q(0)<RIN<ROUT
    assert SAT<RIN
    # In a foreign tube, the i-coordinate is at most TUBE in
    # absolute value, giving distance from c_i >= 9-TUBE.
    assert Q(9)-TUBE>ROUT
    assert Q(9)-Q(1)>RIN
    lo,hi=Q(1,2),Q(17,2)
    for rad in (RIN,ROUT):
        assert rad*rad>TUBE*TUBE
        # Lower cut-sphere branch t=9-sqrt(rad^2-p^2),
        # p^2<=TUBE^2, lies strictly between lo and hi.
        assert Q(9)-rad>lo
        assert rad*rad-TUBE*TUBE>(Q(9)-hi)**2
        # The other sphere branch t>=9 misses the tube.
        assert Q(9)>hi
    # If x is on arm i then x_i>=lo; on arm j!=i,
    # abs(x_i)<=TUBE. Therefore the spokes cannot meet.
    assert lo>TUBE
    x0=(Q(20),Q(20),Q(20))
    assert all(d2(x0,c)>ROUT**2 for c in CENTRES)
    return {
        "centres":[[str(t) for t in c] for c in CENTRES],
        "inner_closed_cut_radius":str(RIN),
        "outer_open_cut_radius":str(ROUT),
        "squared_pair_separation":[str(d) for d in pair_dist2],
        "squared_outer_diameter":str((2*ROUT)**2),
        "inner_strictly_inside_outer":True,
        "satellites_inside_inner_cut":True,
        "foreign_spokes_miss_outer_cut":True,
        "central_ball_misses_inner_cuts":True,
        "tube_meets_both_spherical_cuts_in_single_disk":True,
        "open_cover_coverage":"forall x in E: x in C or x in some S_i",
        "pair_intersections":"U_i intersect U_j = C for i != j",
        "central_pi1_verified":False,
        "satellite_homotopy_verified":False,
        "wild_embedding_verified":False
    }

if __name__=="__main__":
    print(json.dumps(exact_certificate(),indent=2))
