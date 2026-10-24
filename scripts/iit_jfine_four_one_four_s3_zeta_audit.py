#!/usr/bin/env python3
"""Exact jFine 3^4 * 3 * 3^4 centre-gauge, S3, zeta multiplicity audit.

DASHI source: original JFinePhaseQuotientFieldExact nine trits; recentered
S3 ternary actions; C3FourierConjugationExact zeta characters; pointed
Harmonic.CoarseChannel. The permutation module constructed here is NOT
identified with the original Monster 3B representation.
"""
from __future__ import annotations
from itertools import product
from collections import Counter
import hashlib
import json

CORNERS=(0,2,6,8)
EDGES=(1,5,7,3)
COORDS=tuple(product(range(3),repeat=9))

def split(x):
    c=x[4]
    return c, tuple((x[i]-c)%3 for i in EDGES), tuple((x[i]-c)%3 for i in CORNERS)

def join(q):
    c,e,k=q
    a=[c]*9
    for i,v in zip(EDGES,e):a[i]=(c+v)%3
    for i,v in zip(CORNERS,k):a[i]=(c+v)%3
    return tuple(a)

def affine(x,a,b):
    return tuple((a*t+b)%3 for t in x)

def rotation(x):
    a,b,c,d,e,f,g,h,i=x
    return (g,d,a,h,e,b,i,f,c)

def reflection(x):
    a,b,c,d,e,f,g,h,i=x
    return (c,b,a,f,e,d,i,h,g)

def audit():
    assert len(COORDS)==19683
    seen=set()
    orbit_counts=Counter()
    for x in COORDS:
        q=split(x)
        assert join(q)==x
        assert split(rotation(x))[0]==q[0]
        assert split(reflection(x))[0]==q[0]
        for a,b in product((1,2),range(3)):
            transformed=split(affine(x,a,b))
            assert transformed==((a*q[0]+b)%3,
                tuple(a*t%3 for t in q[1]),tuple(a*t%3 for t in q[2]))
            assert rotation(affine(x,a,b))==affine(rotation(x),a,b)
            assert reflection(affine(x,a,b))==affine(reflection(x),a,b)
        if x not in seen:
            o={affine(x,a,b) for a,b in product((1,2),range(3))}
            seen.update(o)
            orbit_counts[len(o)]+=1
    assert seen==set(COORDS)
    assert orbit_counts=={3:1,6:3280}
    assert len({split(x)[1:] for x in COORDS})==6561
    chi_id=len(COORDS)
    chi_ref=sum(affine(x,2,0)==x for x in COORDS)
    chi_cycle=sum(affine(x,1,1)==x for x in COORDS)
    assert (chi_id,chi_ref,chi_cycle)==(19683,1,0)
    m_trivial=(chi_id+3*chi_ref+2*chi_cycle)//6
    m_sign=(chi_id-3*chi_ref+2*chi_cycle)//6
    m_std=(2*chi_id-2*chi_cycle)//6
    assert (m_trivial,m_sign,m_std)==(3281,3280,6561)
    assert m_trivial+m_sign+2*m_std==chi_id
    assert 10*(m_trivial+m_sign)==10*m_std==65610
    # On the *natural 4-coordinate site permutation modules*, a vertical
    # reflection fixes 2 edge sites but no corners. It follows that
    # the two D4 permutation characters, and F3-linear reps, differ.
    fixes=lambda coords:sum(reflection(tuple(int(j==i) for j in range(9)))
       ==tuple(int(j==i) for j in range(9)) for i in coords)
    assert (fixes(EDGES),fixes(CORNERS))==(2,0)
    # Independently compare Burnside and literal joint D4-site x S3-value
    # orbits. The group has 8*6=48 elements.
    identity=tuple(range(9))
    d4=set()
    rot=identity
    for _ in range(4):
        d4.add(rot)
        d4.add(reflection(rot))
        rot=rotation(rot)
    assert len(d4)==8
    burnside=sum(mult*(3**cycles+3*(3**even))
        for mult,cycles,even in ((1,9,0),(2,3,2),(1,5,4),(4,6,3)))
    assert burnside==23520 and burnside//48==490
    seen_joint=set()
    joint_hist=Counter()
    for x in COORDS:
        if x in seen_joint:continue
        orbit={affine(tuple(x[i] for i in perm),a,b)
               for perm in d4 for a,b in product((1,2),range(3))}
        seen_joint.update(orbit)
        joint_hist[len(orbit)]+=1
    assert len(seen_joint)==19683
    assert joint_hist=={3:1,6:6,12:17,24:122,48:344}
    assert sum(joint_hist.values())==490
    # Structural Heisenberg-multiplicity rechart of source-actual C3 orbits.
    # No Weyl/Suzuki action or actual Monster-module identity is smuggled in.
    def to90_729(marker,edges,corners):
        return ((marker,edges[0],edges[1]),
                (edges[2],edges[3],*corners))
    def from90_729(label,six):
        marker,a,b=label
        return marker,(a,b,six[0],six[1]),tuple(six[2:])
    count=0
    for marker,edges,corners in product(
        range(10), product(range(3),repeat=4),product(range(3),repeat=4)
    ):
        assert from90_729(*to90_729(marker,edges,corners)) == (
            marker,edges,corners)
        count+=1
    assert count==65610==90*729
    ret={
      "scope":"finite pointed S3 complex permutation module, not Monster or IIT Phi",
      "fine_size":19683,
      "raw_4_1_4_cardinality":81*3*81,
      "relative_8_trit_quotient":6561,
      "all_fine_codec_roundtrips":19683,
      "checked_S3_gauge_actions":6*19683,
      "S3_orbit_sizes":dict(orbit_counts),
      "S3_permutation_character":{"identity":19683,"transposition":1,"three_cycle":0},
      "complex_irreps_fine":{"trivial":m_trivial,"sign":m_sign,"standard_2d":m_std},
      "complex_irreps_pointed":{"trivial":10*m_trivial,"sign":10*m_sign,
                                 "standard_2d":10*m_std},
      "pointed_C3_zeta_multiplicity_each":65610,
      "heisenberg_90_by_729_chart_roundtrips":count,
      "heisenberg_actual_Weyl_action_identified":False,
      "pointed_states":196830,
      "D4_mirror_fixed_sites_edge_corner":[2,0],
      "D4_times_S3_orbits":490,
      "D4_times_S3_orbit_histogram":dict(joint_hist),
      "D4_times_S3_Burnside_numerator":burnside,
      "D4_edge_corner_natural_modules_inequivalent":True,
      "S3_value_and_D4_site_actions_commute":True,
      "over_F3_distinct_third_roots_exist":False,
      "zeta_plus_zeta_squared_plus_one":0,
      "zeta_times_zeta_squared":1,
      "identifies_existing_Monster_3B_action":False,
      "self_test_completed":True,
    }
    ret["payload_sha256"]=hashlib.sha256(
        json.dumps(ret,sort_keys=True).encode()).hexdigest()
    return ret

if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,indent=2))
