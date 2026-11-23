#!/usr/bin/env python3
"""MG06 369/KK E6 post-E21 source bridge: one photon + faithful U(3).

Original owners: scripts/check_kk_e6_post_e32_sm_global_z6.py and
scripts/check_kk_e6_post_e21_u3_photon.py; #1106 27 first-Tits,
#1241 5D orbifold. This checker invokes the original scripts in a
checkout, so their assertions remain authoritative. The native P3^3
27-vertex spatial incidence is NOT automatically this E6 matter 27.
"""
from collections import Counter
from contextlib import redirect_stdout
from itertools import product
from pathlib import Path
import io
import runpy

ROOT=Path(__file__).resolve().parents[1]


def run_original(path):
    out=io.StringIO()
    with redirect_stdout(out):
        result=runpy.run_path(str(ROOT/path))
    assert 'PASS' in out.getvalue(), (path,out.getvalue())
    return result


def main():
    parent=run_original('scripts/check_kk_e6_post_e32_sm_global_z6.py')
    child=run_original('scripts/check_kk_e6_post_e21_u3_photon.py')
    states=child['states']
    assert len(states)==27 and len(parent['states'])==27
    assert (sum(z[-1]==1 for z in states),sum(z[-1]==-1 for z in states))==(16,11)
    # The original source uses q_z even and q3=3Q=-q_z/2.
    charge=Counter()
    for block,ci,li,ri,triality,qz,hand in states:
        assert qz%2==0
        q3=-qz//2
        assert (triality+q3)%3==0
        charge[(triality,q3,hand)]+=1
    assert sum(charge.values())==27
    assert (0,-3,1) in charge and (1,2,1) in charge
    assert (1,-1,1) in charge and (0,0,1) in charge
    # Full faithful stabilizer kernel on finite covering SU3-centre x U1_z.
    # Representation phases 2*t*c + qz*k over a 3x6 cover.
    kernel=[(c,k) for c,k in product(range(3),range(6))
            if all((2*t*c+qz*k)%6==0 for _,_,_,_,t,qz,_ in states)]
    assert len(kernel)==6
    assert set(kernel)=={(n%3,(5*n)%6) for n in range(6)}
    # The 2:1 z->w=z^2 reduction gives a diagonal 3-element kernel.
    wkernel={(c,k%3) for c,k in kernel}
    assert wkernel=={(0,0),(1,2),(2,1)}
    # Distinguish the original native 369 *spatial* cube incidence from E6 states:
    # both contain 27 entries, but those cardinalities do not establish a map.
    points=list(product((-1,0,1),repeat=3))
    bonds=[(i,j) for i,a in enumerate(points) for j,b in enumerate(points)
           if i<j and sum(abs(x-y) for x,y in zip(a,b))==1]
    assert len(points)==27 and len(bonds)==54
    # There is no charge consumer based solely on the spatial *site count*,
    # since the E6 source includes different q3 at a fixed cardinality.
    q3_values={-z[5]//2 for z in states}
    assert len(q3_values)>1
    print('PASS original parent and post-E21 child source checkers executed')
    print('PASS exact 27-state charge/triality congruence and original 16/11 source parities')
    print('PASS faithful Z6 covering kernel, residual diagonal Z3 and U3 global form')
    print('PASS 369 original spatial 27/54 incidence distinct from E6 matter state labels')
    print('OPEN physical Higgs E-L, global 5D anomalies, physical coupling, 369 state identification')


if __name__=='__main__':main()
