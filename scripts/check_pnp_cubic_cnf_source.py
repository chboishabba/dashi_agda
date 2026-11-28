"""Original local CNF tables -> affine pullback -> connected cubic phase.
Default imports production compiler; --extracted-core replays exact source
slices with original rref/chart/blocks and character functions. The local
fixture widths do not enter normal_fold; in extraction mode it fails closed.
"""
from itertools import product, combinations_with_replacement
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import prod
from random import Random
import argparse,json
if not __debug__:raise SystemExit('refusing optimized execution')

def encode(x):return int(x==1),int(x==2)

def fixture(n,terms):
    # Each monomial has distinct input COPY coordinates; equalities to the
    # actual master trits are imposed through the original F3 syndrome rows.
    # Repeated variables in a monomial use one copy per distinct variable.
    labels=[tuple(sorted(set(m))) for m,a in terms]
    r=sum(map(len,labels));cols=[];F=[];pos=0
    for j in range(n):
        F.append((-(2*j+1),-(2*j+2)))
        for a in (1,2):cols.append(tuple((-a)%3 if i==j else 0 for I in labels for i in I)+(0,))
    for (m,c),I in zip(terms,labels):
        base=len(cols);allowed=set();d=len(I);width=2*d+2
        for x in product(range(3),repeat=d):
            v=dict(zip(I,x));out=c*prod(v[i] for i in m)%3
            allowed.add(tuple(b for a in x for b in encode(a))+encode(out))
        for bits in product(range(2),repeat=width):
            if bits not in allowed:F.append(tuple((base+i+1)*(1 if not a else -1) for i,a in enumerate(bits)))
        for j in range(width):
            cols.append(tuple(j%2+1 if j<2*d and h==pos+j//2 else 0 for h in range(r))+((j%2+1) if j>=2*d else 0,))
        pos+=d
    return tuple(F),tuple(cols),(0,)*r,tuple(range(len(cols)))

def oracle(n,terms,offset):
    H=Counter((offset+sum(a*prod(x[i] for i in m) for m,a in terms))%3 for x in product(range(3),repeat=n))
    return tuple(3*H[i]-3**n for i in range(3))

def main(calc):
    rng=Random(36915);count=0;rows=[]
    P=[((0,1,2),1),((3,4,5),1),((2,6),1),((3,6),2),((6,6),1)]
    cases=[(7,P),(3,[((0,1,2),1)]),(6,[((0,1,2),1),((3,4,5),1)])]
    for n in range(2,6):
        ms=[m for d in (1,2,3) for m in combinations_with_replacement(range(n),d) if len(set(m))>0 and all(m.count(i)<=2 for i in set(m))]
        for _ in range(4):cases.append((n,[(m,rng.randrange(1,3)) for m in rng.sample(ms,min(5,len(ms)))]))
    for n,terms in cases:
        F,cols,t,R=fixture(n,terms)
        for o in range(3):
            v=oracle(n,terms,o);a,b,stats=calc(F,cols,t,o,R,Fraction(1),8,1,10_000_000,degree_cap=3,phase_branch_cap=256)
            assert a==b==v,(n,terms,o,a,v);count+=1
            assert stats['exceptional']==0 and stats['normal_queries']==0;count+=1
            assert stats['branches']==1;count+=1
            rows.append(dict(n=n,variables=len(R),clauses=len(F),offset=o,stats=stats))
        assert calc(F,cols,t,0,R,Fraction(1),8,1,1,degree_cap=3,phase_branch_cap=256) is None;count+=1
    print(json.dumps(dict(checks=count,fixtures=len(cases),connected=rows[:3],max_work=max(r['stats']['work'] for r in rows))))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--extracted-core',type=Path);p.add_argument('--donors',type=Path);a=p.parse_args()
    if a.extracted_core:
        from pnp_phase_separator_exact import choose_separator,restrict_axis,phase_key
        class Refusal(Exception):pass
        def normal_fold(*args):raise AssertionError('unexpected large-block normal fold in extraction')
        env=dict(globals());exec(compile(a.donors.read_text(),str(a.donors),'exec'),env)
        exec(compile(a.extracted_core.read_text(),str(a.extracted_core),'exec'),env)
        calc=env['structured_contrast']
    else:
        from check_pnp_quadratic_phase import structured_contrast as calc
    main(calc)
