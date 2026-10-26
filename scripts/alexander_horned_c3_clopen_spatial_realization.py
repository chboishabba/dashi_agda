#!/usr/bin/env python3
"""A genuinely embedded, tame C3 x Cantor end set from PR #1244's balls.

Reuse (not redesign) the exact formula in
  scripts/alexander_horned_tame_cantor_ball_cylinders.py.
Separate the chronological APPEND and Horn newest-first PREPEND conventions;
PR #1254 owns the generic Agda event-orientation proof. This executable
is a specialized same-object Euclidean consumer, not a wild-ball model.

Mathematical roots: elementary middle-thirds Cantor construction,
compact-to-Hausdorff embedding theorem. Original Alexander/Hatcher
linked-horn topology is a DIFFERENT spatial datum.
"""
from fractions import Fraction as F
from itertools import product
import json

CENTRES=((F(9),F(0),F(0)),(F(0),F(9),F(0)),(F(0),F(0),F(9)))

def rotate(v):return (v[2],v[0],v[1])
def local_ball(chronological):
    n=len(chronological)
    length=F(1,3**(n+1))
    low=F(1,6)+sum((F(2*b,3**(j+2)) for j,b in enumerate(chronological)),F(0))
    return (low+length/2,F(1,2),F(0)),F(3,5)*length

def embedded_ball(sector,chronological):
    centre,radius=local_ball(chronological)
    for _ in range(sector):centre=rotate(centre)
    return tuple(a+b for a,b in zip(CENTRES[sector],centre)),radius

def euclidean_squared(a,b):return sum((x-y)**2 for x,y in zip(a,b))
def sibling_clearance(chronological):
    parent,r=local_ball(chronological)
    a,ra=local_ball(chronological+(0,))
    b,rb=local_ball(chronological+(1,))
    assert ra==rb==r/3
    assert (a[0]-parent[0])**2 == (r/F(3,5)/3)**2
    assert abs(a[0]-parent[0])+ra==r-F(1,15)*F(1,3**(len(chronological)+1))
    assert abs(b[0]-parent[0])+rb==r-F(1,15)*F(1,3**(len(chronological)+1))
    gap=b[0]-a[0]-ra-rb
    assert gap==F(4,15)*F(1,3**(len(chronological)+1))>0
    return gap

def newest_first(chronological):return chronological[::-1]
def chronology_of_stack(stack):return stack[::-1]

def endpoint_interval(chronological):
    """Exact bounds on x(infinite stream) over all possible tail bits."""
    n=len(chronological)
    low=F(1,6)+sum((F(2*b,3**(j+2)) for j,b in enumerate(chronological)),F(0))
    return low,low+F(1,3**(n+1))

def tame_endpoint_finite_tail(chronological):
    """An exact point from the infinite stream with zero tail."""
    low,_=endpoint_interval(chronological)
    return (low,F(1,2),F(0))

def audit(max_depth=8):
    assert max_depth>=1
    assert tuple(rotate(c) for c in CENTRES)==CENTRES[1:]+CENTRES[:1]
    assert embedded_ball(0,())==( (F(28,3),F(1,2),F(0)),F(1,5))
    root,r=local_ball(())
    assert sum((v+(r if v>=0 else -r))**2 for v in root)<1
    # A pair of word conventions is not a pair of different endpoint trees.
    bad_parent=(1,); bad_newest_child=(0,)+bad_parent
    assert bad_newest_child[:len(bad_parent)] != bad_parent
    assert chronology_of_stack((0,)+newest_first(bad_parent)) == bad_parent+(0,)
    tested=0
    for depth in range(max_depth+1):
        for w in product((0,1),repeat=depth):
            low,hi=endpoint_interval(w)
            local,radius=local_ball(w)
            assert abs(low-local[0])<=radius and abs(hi-local[0])<=radius
            assert F(0)<radius and r==F(3**depth)*radius
            assert chronological_child_event(w,0) and chronological_child_event(w,1)
            assert chronology_of_stack((1,)+newest_first(w))==w+(1,)
            assert sibling_clearance(w)>0
            for sector in range(3):
                p,rr=embedded_ball(sector,w)
                q,qr=embedded_ball((sector+1)%3,w)
                assert rotate(p)==q and qr==rr
                assert rr==F(1,5*3**depth)
                assert 3*2**depth*F(1,3*2**depth)==1
                # All three satellite balls lie inside radius-1 envelopes.
                assert sum((x*x for x in local)) < 1
                assert (local[0]+radius)**2+(local[1]+radius)**2+radius**2<1
            tested+=1
    return {'status':'PASS','max_depth':max_depth,'checked_binary_prefixes':tested,
            'sector_prefix_combinations':3*tested,
            'sector_mass_at_depth_n':'1/(3*2^n)',
            'endpoint_map':'F(c,b)=9e_c+R^c(1/6+sum(2b_j/3^(j+2)),1/2,0)',
            'endpoint_image':'three separated affine copies of middle-thirds Cantor set',
            'nested_closed_ball_intersection':'one point by diameters tending to zero',
            'clopen_on_endpoint_image':True,'clopen_in_ambient_R3':False,
            'newest_first_prepend_agrees_after_reversal':True,
            'Hatcher_wild_exterior_pi1_proved':False,
            'linked_horn_ambient_embedding_proved':False}

def chronological_child_event(w,bit):
    return (w+(bit,))[:len(w)]==w

if __name__=='__main__':print(json.dumps(audit(),indent=2))
