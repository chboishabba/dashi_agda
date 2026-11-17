#!/usr/bin/env python3
"""Finite oriented surface exhaustions with reused Cantor prefix coordinates.

Richards (1963) governs final end/genus classification. Here every finite
stage is assembled by attaching explicit oriented surfaces along ONE boundary
circle per parent. Its Euler/genus/boundary accounting is exact. Completion as
an actual topological direct-limit surface, end-homeomorphism and uniqueness
classification remain distinct mathematical obligations.
"""
from dataclasses import dataclass
import json

@dataclass(frozen=True)
class Stage:
    family: str
    depth: int
    genus: int
    boundaries: tuple[tuple[int, ...], ...]
    euler: int

    def verify(self):
        assert self.genus >= 0 and self.boundaries
        assert len(set(self.boundaries)) == len(self.boundaries)
        assert self.euler == 2-2*self.genus-len(self.boundaries)
        return self


def initial(family):
    if family == 'cantor_tree':
        return Stage(family,0,0,((),),1).verify()  # disk
    if family == 'loch_ness_monster':
        return Stage(family,0,0,((),),1).verify()  # disk
    if family == 'jacobs_ladder':
        return Stage(family,0,0,((0,),(1,)),0).verify()  # annulus
    raise ValueError(family)


def extend(s):
    if s.family == 'cantor_tree':
        # Attach one genus-zero three-boundary pair of pants to every
        # outgoing circle (chi=-1, one input, TWO output circles).
        out=tuple(prefix+(side,) for prefix in s.boundaries for side in (0,1))
        nxt=Stage(s.family,s.depth+1,s.genus,out,s.euler-len(s.boundaries))
    elif s.family == 'loch_ness_monster':
        # One genus-one two-boundary cobordism (chi=-2) per round.
        nxt=Stage(s.family,s.depth+1,s.genus+1,s.boundaries,s.euler-2)
    else:
        # One genus-one two-boundary cobordism at EACH of the two ends.
        assert s.family=='jacobs_ladder' and len(s.boundaries)==2
        nxt=Stage(s.family,s.depth+1,s.genus+2,s.boundaries,s.euler-4)
    return nxt.verify()


def audit(max_depth=12):
    results={}
    for family in ('cantor_tree','loch_ness_monster','jacobs_ladder'):
        s=initial(family)
        for n in range(max_depth+1):
            assert s.depth==n
            if family=='cantor_tree':
                assert s.genus==0 and len(s.boundaries)==2**n
                assert s.euler==2-2**n
                assert set(s.boundaries)==set(tuple((k>>j)&1 for j in range(n-1,-1,-1)) for k in range(2**n))
            elif family=='loch_ness_monster':
                assert s.genus==n and len(s.boundaries)==1 and s.euler==1-2*n
            else:
                assert s.genus==2*n and len(s.boundaries)==2 and s.euler==-4*n
            if n<max_depth: s=extend(s)
        results[family]={'checked_depths':max_depth+1,
                         'last_depth':max_depth,
                         'last_genus':s.genus,
                         'last_boundary_count':len(s.boundaries),
                         'last_euler':s.euler,
                         'full_surface_constructed':False}
    return results


if __name__=='__main__':
    print(json.dumps({'results':audit(),
          'status':'PASS finite collar-gluing Euler/genus/prefix checks; infinite surface/end theorem OPEN'},
          indent=2,sort_keys=True))
