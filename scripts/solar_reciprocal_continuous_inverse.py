"""Exact continuous four-phase inverse, consuming committed switch owner.
Fixed target quadratures: exhaustive signed affine feasibility, not global optimization.
"""
import sympy as S
from fractions import Fraction as F
from math import gcd,lcm
from itertools import product
from solar_reciprocal_periodic_switch import B,C,D,h,FORCES,cycle,reverse_schedule,velocity_budget,passive_optimum


def affine_feasible(exprs,variables):
    """Fourier–Motzkin elimination with exact rational witness backsolve."""
    def primitive(row):
        row=tuple(map(F,row));d=lcm(*(x.denominator for x in row))
        z=tuple(int(x*d) for x in row);g=gcd(*z)
        return tuple(x//g for x in z) if g else z
    rows=set()
    for e in exprs:
        p=S.Poly(e,*variables);rows.add(primitive([p.coeff_monomial(v) for v in variables]+[p.coeff_monomial(1)]))
    history=[]
    for _ in variables:
        if any(not any(r[:-1]) and r[-1]<0 for r in rows):return None
        rows={r for r in rows if any(r[:-1])};history.append(rows)
        pos=[r for r in rows if r[0]>0];neg=[r for r in rows if r[0]<0]
        rows={r[1:] for r in rows if r[0]==0}
        rows.update(primitive([-n[0]*a+p[0]*b for a,b in zip(p[1:],n[1:])]) for p in pos for n in neg)
    if any(r[0]<0 for r in rows):return None
    tail=[]
    for rows in reversed(history):
        lo=[];hi=[]
        for r in rows:
            val=sum(a*b for a,b in zip(r[1:-1],tail))+r[-1]
            if r[0]>0:lo.append(-val/S.Integer(r[0]))
            elif r[0]<0:hi.append(-val/S.Integer(r[0]))
            else:assert val>=0
        x=max(lo) if lo else min(hi) if hi else S.Integer(0)
        assert not hi or x<=min(hi)
        tail.insert(0,x)
    sub=dict(zip(variables,tail));assert all(e.subs(sub)>=0 for e in exprs)
    return sub

def inverse(a,b):
    a,b=map(S.Matrix,(a,b));u=S.Matrix([2,1,1])
    if (u.T*a)[0]!=1 or (u.T*b)[0]!=0:return dict(status='EMPTY_AFFINE')
    cx,cy,sx,sy=S.symbols('cx cy sx sy',real=True)
    c=S.Matrix([cx,-cx-cy,cy]);s=S.Matrix([sx,-sx-sy,sy])
    qs=[c-a-b,c+a-b,c+a+b,c-a+b,c-a-b]
    vs=[a-b+s,a+b-s,-a+b+s,-a-b-s,a-b+s]
    states=[S.Matrix.vstack(q,v) for q,v in zip(qs,vs)]
    ext=[[],[]];force=[[],[]]
    for k,(x,y,f) in enumerate(zip(states,states[1:],FORCES)):
        q=(x[:3,:]+y[:3,:])/2;v=(x[3:,:]+y[3:,:])/2
        rhs=f-D*v-q-(y[3:,:]-x[3:,:])/h
        assert S.expand(sum(rhs))==0
        for j,(bond,t) in enumerate(((B,rhs[0]),(C,-rhs[2]))):
            ext[j].append(S.expand((bond.T*q)[0]));force[j].append(S.expand(t))
    # Each bond extension shares a single affine offset. Sort the four
    # constant offsets; only five ordered sign patterns per bond suffice.
    patterns=[]
    for es in ext:
        order=sorted(range(4),key=lambda k:es[k].subs({cx:0,cy:0}))
        patterns.append([tuple(-1 if k in order[:j] else 1 for k in range(4)) for j in range(5)])
    excluded=0
    for signs in product(*patterns):
        inequalities=[]
        for j in range(2):
            for k in range(4):
                sg=signs[j][k];e=ext[j][k];f=force[j][k]
                inequalities.extend([sg*f,sg*(e-f)])
        sub=affine_feasible(inequalities,(cx,cy,sx,sy))
        if sub is None:excluded+=1;continue
        st=[x.subs(sub) for x in states];sched=reverse_schedule(st)
        assert sched is not None
        sched=[tuple(0 if x is None else x for x in p) for p in sched]
        rec=cycle(sched);assert rec['status']=='PERIODIC' and rec['states']==st
        return dict(status='INHABITED',schedule=sched,receipt=rec,excluded_before_witness=excluded)
    return dict(status='EMPTY_FIXED_TARGET',excluded=excluded)


def stable_power(M,limit=32):
    """Exact sufficient Schur certificate; failure is unresolved."""
    P=S.eye(M.rows)
    for n in range(1,limit+1):
        P=P*M;norm=sum(x*x for x in P)
        if norm<1:return dict(certified=True,power=n,norm_squared=norm)
    return dict(certified=False,power=limit)


def recovery_buffer(work,eta):
    """Full phase-resolved ideal buffer, no external purchase. Export at end."""
    eta=S.Rational(eta);assert 0<=eta<=1
    prefix=[S.Integer(0)]
    for w in work:prefix.append(prefix[-1]+eta*max(0,-w)-max(0,w))
    export=prefix[-1]
    if export<0:return dict(restored=False,shortfall=-export)
    prefix.append(prefix[-1]-export);start=-min(prefix);state=[start+x for x in prefix]
    assert state[0]==state[-1] and min(state)==0
    return dict(restored=True,export=export,capacity=max(state),initial=start,state=state)


def run():
    p=cycle([(1,1)]*4);a,b=p['vel'][:2];z=inverse(a,b);assert z['status']=='INHABITED'
    assert z['receipt']['vel'][:2]==[a,b]
    center=velocity_budget(p)['center'];z=inverse(center,S.zeros(3,1));assert z['status']=='EMPTY_FIXED_TARGET' and z['excluded']==25;print('center',z['status'],z['excluded'])
    sched=[(0,1),(0,1),(0,1),(1,0)];r=cycle(sched);st=stable_power(r['monodromy']);assert st['certified']
    eta=S.Rational(3,10);buf=recovery_buffer(r['mod'],eta);assert buf['restored']
    assert r['receiver']+buf['export']==r['gross_net']+eta*r['recover']>passive_optimum()
    print('stable power',st['power'],'norm squared',float(st['norm_squared']),'recovery export',buf['export'],'capacity',buf['capacity'],'net',r['receiver']+buf['export'])
    interior=[(S.Rational(1,100),S.Rational(99,100))]*3+[(S.Rational(99,100),S.Rational(1,100))]
    r=cycle(interior);buf=recovery_buffer(r['mod'],eta);st=stable_power(r['monodromy'])
    assert st['certified'] and buf['restored'] and r['receiver']+buf['export']>passive_optimum()
    print('interior gain',r['receiver']+buf['export']-passive_optimum(),'net',float(r['receiver']+buf['export']),'threshold',float((passive_optimum()-r['gross_net'])/r['recover']))
    print('CONTINUOUS_INVERSE_PASS')
if __name__=='__main__':run()
