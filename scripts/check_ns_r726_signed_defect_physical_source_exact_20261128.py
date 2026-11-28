#!/usr/bin/env python3
"""Original periodic R406/R652/R687/R722/R723/R726 signed defect.

C=1 complete ordered p+q=k Galerkin Fourier source, real-conjugate,
divergence-free, exact helical eigenprojectors in Q(i,sqrt2,sqrt3).
The two signed witnesses prove the UNIVERSAL ZERO-defect instantaneous
comparison is false on physical states. Finite Galerkin ODE continuity then
extends the strict positive sign to some short physical-time interval.
No cutoff-uniform estimate, native Agda field extension or Clay theorem.
"""
from collections import defaultdict
from itertools import product
from sympy import Matrix, I, S, sqrt, simplify, expand, re, conjugate

CUTOFF=1
MODES=[k for k in product(range(-1,2), repeat=3) if k != (0,0,0)]
INPUT_MODES=[(0,0,0)]+MODES
ZERO=Matrix([0,0,0])
def add(p,q):return tuple(x+y for x,y in zip(p,q))
def neg(k):return tuple(-x for x in k)
def ksq(k):return sum(x*x for x in k)
def dot(u,v):return sum(u[i]*v[i] for i in range(3))
def vexp(v):return Matrix([expand(t) for t in v])
def transverse(k,v):
    kvec=Matrix(k)
    return vexp(v-kvec*dot(kvec,v)/ksq(k))
def helicity(k,v,sign):
    return vexp((transverse(k,v)+sign*I*Matrix(k).cross(v)/sqrt(ksq(k)))/2)
def pair(u,v):return simplify(re(sum(conjugate(u[i])*v[i] for i in range(3))))

def physical_certificate(positive_modes):
    u={k:Matrix(v) for k,v in positive_modes.items()}
    for k,v in list(u.items()):
        assert simplify(dot(k,v)) == 0
        assert neg(k) not in u
        u[neg(k)]=v.conjugate()
    assert u[(1,0,0)] != ZERO
    nonlinear=defaultdict(lambda:ZERO.copy())
    for p,q in product(u,repeat=2):
        k=add(p,q)
        if k != (0,0,0) and max(map(abs,k)) <= CUTOFF:
            nonlinear[k]+=dot(u[p],Matrix(q))*u[q]
    n={k:vexp(-I*transverse(k,w)) for k,w in nonlinear.items()}
    hp={sign:{k:helicity(k,v,sign) for k,v in u.items()} for sign in (+1,-1)}
    hn={sign:{k:helicity(k,v,sign) for k,v in n.items()} for sign in (+1,-1)}
    def get(tab,k):return tab.get(k,ZERO)
    def A(p,q):return vexp(get(hp[+1],p).cross(get(hp[-1],q)))
    def B(p,q):return vexp(get(hn[+1],p).cross(get(hp[-1],q))+
                            get(hp[+1],p).cross(get(hn[-1],q)))
    blocks=defaultdict(list)
    incidence_count=0
    for k in MODES:
        for p in INPUT_MODES:
            q=tuple(k[j]-p[j] for j in range(3))
            if q not in INPUT_MODES:continue
            incidence_count+=1
            # Retain both original zero-input incidences. Mean-zero velocity
            # and divergence-free unforced N_0 make their A/M/B/D exactly zero.
            if p==(0,0,0) or q==(0,0,0):continue
            if not ((p in u and q in u) or (p in n and q in u) or
                    (p in u and q in n)):continue
            a=A(p,q)
            m=vexp(2*(a+A(q,p)))
            d=vexp(2*(B(p,q)+B(q,p)))
            if m==ZERO and d==ZERO:continue
            blocks[k].append((a,m,d,ksq(p)+ksq(q)))
    full=diag=lift=comm=companion=S.Zero
    for items in blocks.values():
        a_sum=sum((x[0] for x in items),ZERO.copy())
        m_sum=sum((x[1] for x in items),ZERO.copy())
        d_sum=sum((x[2] for x in items),ZERO.copy())
        assert vexp(m_sum-4*a_sum)==ZERO
        comm+=2*pair(a_sum,d_sum/4)
        for i,(a,m,d,rate) in enumerate(items):
            for j,(aa,mm,dd,rr) in enumerate(items):
                if i<j:
                    companion+=S.Half*(pair(d,mm)+pair(m,dd))/(rate+rr)
                if d==ZERO or mm==ZERO:continue
                weight=pair(d,mm)/(rate+rr)
                full+=weight
                lift+=(rate+rr)*weight
                if i==j:diag+=weight
    vals={name:simplify(v) for name,v in {
        'forcing_full':full,'forcing_diag':diag,'rate_lifted_full':lift,
        'coherent_commutator':comm,'r406':4*companion,
        'combined':12*comm,'defect':4*companion-12*comm,
        'numerator':4*full-4*diag-24*comm,
    }.items()}
    assert simplify(4*companion-2*(full-diag))==0
    assert simplify(lift-8*comm)==0
    assert simplify(4*full-2*(4*companion)-4*diag)==0
    assert simplify(2*vals['defect']-vals['numerator'])==0
    assert incidence_count==sum(
        sum(1 for p in INPUT_MODES if tuple(k[j]-p[j] for j in range(3)) in INPUT_MODES)
        for k in MODES)
    return vals,incidence_count

NEGATIVE={
    (1,0,0):(0,-1-I,1+2*I),
    (0,1,0):(2*I,0,2-2*I),
    (1,1,0):(-1-I/2,1+I/2,-1),
    (0,0,1):(-1,2+2*I,0),
}
POSITIVE={
    (1,0,0):(0,I,-1-2*I),
    (0,1,0):(-2+I,0,1-I),
    (1,1,0):(-S.Half,S.Half,1+I),
    (1,0,1):(S(3)/2+2*I,2*I,-S(3)/2-2*I),
    (0,0,1):(1,-1-I,0),
}

def main():
    n,ncells=physical_certificate(NEGATIVE)
    p,pcells=physical_certificate(POSITIVE)
    assert ncells==pcells==316
    # Exact algebraic signs, not floating heuristic. SymPy's real algebraic
    # number comparator certifies the roots and the strict inequalities.
    assert n['defect'].is_negative is True,n['defect']
    assert p['defect'].is_positive is True,p['defect']
    print('PASS R726 physical-real exact source',ncells,
          'ordered original incidences and both strict defect signs')
    print('negative:',n['defect'])
    print('positive:',p['defect'])
    print('R652, R687, R726 signed numerator identities all PASS')
if __name__=='__main__': main()
