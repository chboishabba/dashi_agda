"""Exact four-phase uniform-permittivity transverse inverse, all phases.
Projection by rational halfspaces, then nearest point to ideal work centre.
The ideal signed pump ceiling is not a physical actuator or stability proof.
"""
from fractions import Fraction as F
from itertools import product,combinations
from math import gcd,lcm
import sympy as S
from solar_coarse_source_cycle import fixture,static_optimum
from solar_gauss_ade_weld import augmented_step


def chart(d,c,q,r):
    h,a,o,g,s,l,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'))
    w=d[1].T;k=(w.T*w)[0];assert d[1].rows==1 and k>0
    t,D0,B0=S.symbols('t D0 B0',real=True);inc=[1,0,-1,0];em=[q,r,-q,-r]
    E=[t];B=[B0]
    for e in em:E.append(S.expand(2*e-E[-1]));B.append(S.expand(B[-1]-h*k*e))
    assert E[-1]==t and B[-1]==B0
    b0=S.solve(sum(B[:4]),B0)[0];B=[S.expand(x.subs(B0,b0)) for x in B]
    P=S.symbols('P0:4',real=True);V=S.symbols('V0:4',real=True);eq=[]
    for i,e in enumerate(em):
        j=(i+1)%4;pm=(P[i]+P[j])/2;vm=(V[i]+V[j])/2
        eq += [P[j]-P[i]-h*vm,V[j]-V[i]-h*(a*e-g*vm-o*pm)]
    sol=S.solve(eq,(*P,*V),dict=True)[0];P=[sol[x] for x in P];V=[sol[x] for x in V]
    D=[D0]
    for i,e in enumerate(em):D.append(S.expand(D[-1]+h*((B[i]+B[i+1])/2-(s+l+p*p)*e+2*p*inc[i])))
    assert D[-1]==D0
    return t,D0,E,B,P,V,D,w,em


def inequalities(z,lo,hi,signs):
    t,D0,E,B,P,V,D,w,em=z;lower=[];upper=[];out=[]
    for i,sign in enumerate(signs):
        e=E[i];v=D[i]-D0-P[i];out.append(sign*e)
        lower.append((lo if sign==1 else hi)*e-v);upper.append((hi if sign==1 else lo)*e-v)
    return out+[u-l for u in upper for l in lower],lower,upper


def primitive(row):
    row=tuple(map(F,row));d=lcm(*(x.denominator for x in row));v=tuple(int(x*d) for x in row);g=gcd(*v)
    return tuple(x//g for x in v) if g else v


def project(z,lo,hi,signs,q,r):
    t=z[0];ineq,_,_=inequalities(z,lo,hi,signs);low=[];high=[];flat=[]
    for x in ineq:
        x=S.Poly(x,t,q,r);row=tuple(F(x.coeff_monomial(m)) for m in (t,q,r,1));a,*b=row
        if a>0:low.append(tuple(v/a for v in b))
        elif a<0:high.append(tuple(v/(-a) for v in b))
        else:flat.append(tuple(b))
    rows={primitive(v) for v in flat+[tuple(a+b for a,b in zip(l,h)) for l in low for h in high]}
    if any(a==b==0 and c<0 for a,b,c in rows):return None
    return sorted((a,b,c) for a,b,c in rows if a or b)


def nearest(rows,centre):
    x0,y0=centre;points={(x0,y0)}
    for a,b,c in rows:
        d=F(a*x0+b*y0+c,a*a+b*b);points.add((x0-a*d,y0-b*d))
    for (a,b,c),(d,e,f) in combinations(rows,2):
        det=a*e-b*d
        if det:points.add((F(b*f-c*e,det),F(c*d-a*f,det)))
    valid=[(x,y) for x,y in points if all(a*x+b*y+c>=0 for a,b,c in rows)]
    if not valid:return None
    return min(valid,key=lambda v:((v[0]-x0)**2+(v[1]-y0)**2,v))


def reopen(d,c,z,lo,hi,signs,q,r,xy):
    t,D0,E,B,P,V,D,w,em=z;sub={q:S.Rational(xy[0]),r:S.Rational(xy[1])};ineq,lower,upper=inequalities(z,lo,hi,signs)
    tl,th=-S.oo,S.oo
    for v in ineq:
        v=S.expand(v.subs(sub));a=v.coeff(t);b=v.subs(t,0)
        if a>0:tl=max(tl,-b/a)
        elif a<0:th=min(th,-b/a)
        else:assert b>=0
    assert tl<=th;sub[t]=tl if tl!=-S.oo else th if th!=S.oo else S.Integer(0)
    sub[D0]=max(v.subs(sub) for v in lower);assert sub[D0]<=min(v.subs(sub) for v in upper)
    E,B,P,V,D,em=([S.simplify(v.subs(sub)) for v in seq] for seq in (E,B,P,V,D,em))
    eps=[(D[i]-P[i])/E[i] if E[i] else lo for i in range(4)];eps.append(eps[0]);assert all(lo<=v<=hi for v in eps)
    h,a,o,g,s,l,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'));inc=[1,0,-1,0]
    x=S.Matrix.vstack(E[0]*w,S.Matrix([B[0]]),P[0]*w,V[0]*w);initial=x;W=[]
    for i in range(4):
        step=augmented_step(d,[eps[i]]*len(w),[eps[i+1]]*len(w),[S.Integer(1)],a,o,g,s+p*p,l,x,2*p*inc[i]*w,S.zeros(len(w),1),h)
        assert (x[:len(w),:]+step['state'][:len(w),:])/2==em[i]*w
        W.append(step);x=step['state']
    assert x==initial
    return dict(eps=eps,ideal=sum(v['useful']-v['modulation'] for v in W),gross=sum(v['useful']-max(0,v['modulation']) for v in W))


def global_ideal(d,c,lo,hi):
    lo,hi=map(S.Rational,(lo,hi));assert 0<lo<=hi
    q,r=S.symbols('q r',real=True);z=chart(d,c,q,r)
    h,a,o,g,s,l,p=(c[k] for k in ('h','alpha','omega2','gamma','sigma','load','p'))
    k=(z[-2].T*z[-2])[0];delta=2*S.I/h;v=a*delta/(delta**2+g*delta+o)
    R=S.simplify(p*p+s+g/a*v*S.conjugate(v));assert R>0
    centre=(F(p/R),F(0));opts=[];count=0
    for signs in product((-1,1),repeat=4):
        rows=project(z,lo,hi,signs,q,r)
        if rows is None:continue
        xy=nearest(rows,centre)
        if xy is None:continue
        count+=1;x,y=map(S.Rational,xy)
        net=S.simplify(2*h*k*(2*p*x-R*(x*x+y*y)))
        opts.append((net,signs,xy))
    assert opts
    net,signs,xy=max(opts,key=lambda a:a[0]);w=reopen(d,c,z,lo,hi,signs,q,r,xy);assert net==w['ideal']
    return dict(upper=net,witness=w,quadrature=xy,feasible_sectors=count,total_sectors=16,physical_admission=False)


def run():
    d,c=fixture();r=global_ideal(d,c,1,2);P=static_optimum(d,c,1,2,2*c['h']*(d[1]*d[1].T)[0])['useful']
    print(dict(status='GLOBAL_QUADRATURE_PASS',ideal_upper=str(r['upper']),ideal_upper_float=float(r['upper']),gross_witness=float(r['witness']['gross']),passive=float(P),gain_upper=float(r['upper']-P),gain_witness=float(r['witness']['gross']-P),sectors=r['feasible_sectors'],quadrature=list(map(str,r['quadrature'])),eps=list(map(str,r['witness']['eps'])),physical_admission=False))
if __name__=='__main__':run()
