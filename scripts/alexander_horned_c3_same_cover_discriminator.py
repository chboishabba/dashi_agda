#!/usr/bin/env python3
"""Exact collar algebra and finite-observable collision for horned C3.

Source roots: Alexander (1924), Hatcher AT Example 2B.2,
Lippert's supported construction. The rational C3 cut is DASHI PR #1244.
PR #1254 supplies the separate geometric/ancestry no-promotion precedent.

No program can infer an infinite wild-satellite pi1 from these cut
inequalities. Tame and wild satellite replacements agree on the cut
regions when both are contained in the same inner reference balls.
"""
import json
from fractions import Fraction as F
from itertools import combinations
import sympy as sp

C = ((F(9),F(0),F(0)),(F(0),F(9),F(0)),(F(0),F(0),F(9)))
INNER, OUTER, TUBE = F(15,4),F(17,4),F(1,4)

def squared_distance(a,b):
    return sum((x-y)**2 for x,y in zip(a,b))

def outside_reference_solid(x):
    """Tame common-core scaffold outside inner cut balls only."""
    central = sum(t*t for t in x) <= 1
    tubes = any(F(1,2)<=x[i]<=F(17,2) and
                sum(x[j]**2 for j in range(3) if i!=j) <= TUBE*TUBE
                for i in range(3))
    satellite_envelopes = any(squared_distance(x,c) <= 1 for c in C)
    return not (central or tubes or satellite_envelopes)

def cover_membership(x,inner=INNER,outer=OUTER):
    ds=[squared_distance(x,c) for c in C]
    central=all(d>inner*inner for d in ds)
    sectors=[d<outer*outer for d in ds]
    return central,sectors,[central or s for s in sectors]

def symbolic_shell_identities():
    r,a,z1,z2=sp.symbols('r a z1 z2', positive=True, real=True)
    s=z1*z1+z2*z2
    t=9+r*(1-s)/(1+s)
    u=2*r*z1/(1+s);v=2*r*z2/(1+s)
    assert sp.cancel((t-9)**2+u**2+v**2-r**2)==0
    assert sp.cancel(u/(t-9+r)-z1)==0
    assert sp.cancel(v/(t-9+r)-z2)==0
    R=(r+sp.sqrt(r*r-a*a))/a
    assert sp.simplify((2*r*R-a*(1+R*R)).expand())==0
    tR=9+r*(1-R*R)/(1+R*R)
    assert sp.simplify(tR-(9-sp.sqrt(r*r-a*a)))==0
    assert sp.simplify(4*r*r*R*R/(1+R*R)**2-a*a)==0
    return 5

def audit():
    assert all(squared_distance(C[i],C[j])==162
               for i,j in combinations(range(3),2))
    assert 4*OUTER*OUTER<162 and INNER<OUTER
    assert INNER>1 and F(9)-TUBE>OUTER
    assert F(9)-OUTER>F(1,2) and F(9)-INNER<F(17,2)
    # Round and supported wild satellites inside the radius-1
    # reference balls yield identical common-core cuts and overlaps.
    # This is an agreement of *local sets*, not a claim they have
    # the same exterior fundamental group.
    n=0
    for x0 in range(-2,16):
        for x1 in range(-2,16):
            for x2 in range(-2,16):
                x=(F(x0),F(x1),F(x2))
                if not outside_reference_solid(x): continue
                cen,sectors,U=cover_membership(x)
                assert any(U)
                assert sum(sectors)<=1
                for i,j in combinations(range(3),2):
                    assert (U[i] and U[j])==cen
                n+=1
    # Fail-closed controls: lost radial margin causes a coverage hole.
    witness=(F(13),F(0),F(0))
    assert outside_reference_solid(witness)
    assert not any(cover_membership(witness,F(4),F(4))[2])
    # Overlarge sector cuts overlap despite a perfectly tame core.
    midpoint=(F(9,2),F(9,2),F(0))
    assert outside_reference_solid(midpoint)
    assert sum(cover_membership(midpoint,INNER,F(7))[1])>=2
    ids=symbolic_shell_identities()
    return dict(status='PASS',symbolic_shell_identities=ids,
      exact_rational_lattice_points=n,
      good_open_cover=True,
      missing_radial_margin_control='coverage fails',
      excessive_outer_radius_control='satellites intersect',
      same_cut_tame_wild_collision='indistinguishable to this checker',
      geometric_satellite_pi1_verified=False,
      infinite_wild_embedding_machine_certified=False)

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
