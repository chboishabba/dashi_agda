#!/usr/bin/env python3
"""AK reference physical vector and radion: direct linearized Ricci replay.
Classical Einstein/Israel, ADM and warped mode decomposition. Not a nonlinear
Hopf solution or a completeness theorem for all scalar harmonics.
"""
import sympy as S
from itertools import product
n,t,x,y,r=S.symbols('n t x y r',real=True)
h=S.Rational(4,5); b=S.Function('b')(n); k=S.diff(b,n)/b
coords=[n,t,x,y,r]; ids=range(5)
g=S.diag(1,-b*b/(h*r)**2,b*b/(h*r)**2,b*b/(h*r)**2,b*b/(h*r)**2); gi=g.inv()

def simp(q):
    q=S.expand(q).subs(S.diff(b,n,2),b).subs(S.diff(b,n)**2,b*b-h*h)
    return S.factor(q)
G={(a,i,j):S.factor(gi[a,a]*(S.diff(g[a,j],coords[i])+S.diff(g[a,i],coords[j])-S.diff(g[i,j],coords[a]))/2) for a,i,j in product(ids,repeat=3)}
G={key:v for key,v in G.items() if v!=0}
def gamma(a,i,j):return G.get((a,i,j),0)

def linE(p):
    # Independent linearized Christoffel and Ricci, no Gauss decomposition.
    dp_inv=-gi*p*gi
    dg={}
    for a,i,j in product(ids,repeat=3):
        v=gi[a,a]*(S.diff(p[a,j],coords[i])+S.diff(p[a,i],coords[j])-S.diff(p[i,j],coords[a]))/2
        v+=sum(dp_inv[a,l]*g[l,l]*gamma(l,i,j) for l in ids)
        v=S.factor(v)
        if v!=0: dg[a,i,j]=v
    def D(a,i,j):return dg.get((a,i,j),S.S.Zero)
    out=S.zeros(5)
    for i,j in product(ids,repeat=2):
        if j<i:continue
        v=sum(S.diff(D(a,i,j),coords[a])-S.diff(D(a,i,a),coords[j]) for a in ids)
        v+=sum(D(a,a,l)*gamma(l,i,j)+gamma(a,a,l)*D(l,i,j)-D(a,j,l)*gamma(l,i,a)-gamma(a,j,l)*D(l,i,a) for a,l in product(ids,repeat=2))
        out[i,j]=out[j,i]=simp(v+4*p[i,j])
    return out

def radion():
    chi=S.Function('chi')(t,x,y,r); psi=chi/b**2
    p=S.diag(-4*psi,*[2*psi*g[i,i] for i in range(1,5)])
    E=linE(p)
    box=h*h*(r*r*(-chi.diff(t,2)+chi.diff(x,2)+chi.diff(y,2)+chi.diff(r,2))-2*r*chi.diff(r))
    F=box-4*h*h*chi
    print('radion ratios:',[S.simplify(E[i,i]/F) for i in ids])
    assert all(E[i,j]==0 for i,j in product(ids,repeat=2) if i!=j)
    assert simp(E[0,0]-2*F/b**4)==0
    for i in range(1,5):assert simp(E[i,i]+g[i,i]*F/b**4)==0
    # normal mixed curvature variation delta A=psi'-k phi, phi=-2psi
    assert S.simplify(psi.diff(n)+2*k*psi)==0
    # Reduced EH+GHY+tension action evaluated on exact exponential path.
    e,c,j,K=S.symbols('eps chi j k',real=True); P=e*c
    normal=S.diff(12*S.exp(6*P)*(K-2*K*P)**2+12*S.exp(2*P),e,2).subs(e,0)/2
    assert S.expand(normal-24*(1-K*K)*c*c)==0
    seam=S.diff(6*j*S.exp(4*P),e,2).subs(e,0)/2
    assert seam==48*j*c*c
    I=S.Rational(15,8); j0=-S.Rational(6,5)
    assert h*h*I==-j0
    assert 24*h*h*I+48*j0==-24*h*h*I
    print('PASS all 15 direct radion equations; seam and positive scalar kinetic action, I=',I)

def vector():
    # Two independent transverse components, with arbitrary t,r dependence.
    # V is a base covector; metric shift perturbation p_na=b^2 Z_a.
    A=S.Function('A')(t,r); B=S.Function('B')(t,r)
    p=S.zeros(5); p[0,2]=p[2,0]=A/b**2; p[0,3]=p[3,0]=B/b**2
    E=linE(p)
    for i,j in product(ids,repeat=2):
        if (i,j) not in [(0,2),(2,0),(0,3),(3,0)]:assert E[i,j]==0,(i,j,E[i,j])
    # Proca transverse equation in AdS4 Poincare chart: r²(-A_tt+A_rr)-6A=0.
    for i,U in [(2,A),(3,B)]:
        F=h*h*(r*r*(-U.diff(t,2)+U.diff(r,2))-6*U)
        assert simp(E[0,i]+F/(2*b**4))==0,(E[0,i],F)
    # b^-4 normal profile, continuous mean K vector, Israel derivative jump zero.
    assert S.simplify(S.diff(b**-4,n)+4*k*b**-4)==0
    print('PASS all 15 direct vector equations (two arbitrary transverse components)')
    # ∫ b^-4 on the original proper interval; positive Proca normalization.
    I=S.Rational(5,4)**4*2*(S.Rational(3,5)-S.Rational(3,5)**3/3)
    assert I==S.Rational(165,64)
    print('PASS positive vector normalization I=',I)

if __name__=='__main__':radion();vector()
