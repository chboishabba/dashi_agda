"""Coarse all-continuous upper bound by exact separation of the ideal centre.
Every signed bond sector contributes a valid affine halfspace certificate.
"""
from fractions import Fraction as F
from math import gcd,lcm
from itertools import product
import sympy as S
from solar_reciprocal_periodic_switch import B,C,D,h,FORCES,cycle,velocity_budget


def primitive(row):
    row=tuple(map(F,row));d=lcm(*(x.denominator for x in row));z=tuple(int(x*d) for x in row);g=gcd(*z)
    return tuple(x//g for x in z) if g else z


def project(rows,count,centre):
    # Only need one valid separator per sector, not the full projected polytope.
    # Keep strongest inequality at centre for each remaining hidden normal.
    for remaining in range(count,0,-1):
        chosen={}
        for row in rows:
            key=row[:remaining];g=gcd(*key)
            value=sum(x*y for x,y in zip(row[remaining:-1],centre))+row[-1]
            if not g:
                if value<0:return {row[remaining:]}
                continue
            k=tuple(x//g for x in key);score=value/g
            if k not in chosen or score<chosen[k][0]:chosen[k]=(score,row)
        rows={r for _,r in chosen.values()}
        pos=[r for r in rows if r[0]>0];neg=[r for r in rows if r[0]<0]
        rows={r[1:] for r in rows if r[0]==0}
        rows.update(primitive([-n[0]*a+p[0]*b for a,b in zip(p[1:],n[1:])]) for p in pos for n in neg)
    return rows


def global_gap():
    hidden=S.symbols('cx cy sx sy',real=True);cx,cy,sx,sy=hidden
    av=S.symbols('a0:3',real=True);bv=S.symbols('b0:3',real=True);a,b=map(S.Matrix,(av,bv))
    c=S.Matrix([cx,-cx-cy,cy]);s=S.Matrix([sx,-sx-sy,sy]);variables=hidden+av+bv
    qs=[c-a-b,c+a-b,c+a+b,c-a+b,c-a-b]
    vs=[a-b+s,a+b-s,-a+b+s,-a-b-s,a-b+s]
    rows=[]
    for k,f in enumerate(FORCES):
        q=(qs[k]+qs[k+1])/2;v=(vs[k]+vs[k+1])/2
        rhs=f-D*v-q-(vs[k+1]-vs[k])/h
        for bond,t in ((B,rhs[0]),(C,-rhs[2])):
            e=(bond.T*q)[0]
            pair=[]
            for z in (t,e-t):
                p=S.Poly(z,*variables);pair.append(primitive([p.coeff_monomial(v) for v in variables]+[p.coeff_monomial(1)]))
            rows.append(pair)
    centre=(F(1,6),F(1,12),F(7,12),F(0),F(0),F(0));cert=[];maxrows=0
    for signs in product((-1,1),repeat=8):
        projected=project([tuple(sg*x for x in row) for sg,pair in zip(signs,rows) for row in pair],4,centre);maxrows=max(maxrows,len(projected))
        choices=[]
        for row in projected:
            residual=sum(x*y for x,y in zip(row[:-1],centre))+row[-1]
            if residual>=0:continue
            norm2=sum(x*x for x in row[:-1]);choices.append((None if norm2==0 else residual*residual/norm2,row))
        assert choices,'unseparated sector'
        if any(v is None for v,row in choices):cert.append((signs,None,next(row for v,row in choices if v is None)))
        else:
            dist,row=max(choices);cert.append((signs,dist,row))
    dist=min(v for signs,v,row in cert if v is not None)
    assert dist>0
    cap=F(5,6)-4*dist
    return dict(cap=cap,distance_squared=dist,certificates=cert,max_projected_rows=maxrows)


def run():
    r=global_gap();assert len(r['certificates'])==256
    print('CONTINUOUS_GLOBAL_GAP_PASS',r['distance_squared'],r['cap'],float(r['cap']),r['max_projected_rows'])
if __name__=='__main__':run()
