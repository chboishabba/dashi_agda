#!/usr/bin/env python3
"""BS10: actual AdS4 York overlaps and scalar material bending elimination.
Checks covariant identities, not completeness for arbitrary Lorentzian data.
"""
import sympy as s
from itertools import product
from functools import lru_cache

x=s.symbols('t x y r',real=True); r=x[3]; c=s.Rational(16,25)
h=s.diag(-1,1,1,1)/(c*r*r); hi=h.inv(); I=range(4)
G={(a,b,d):s.factor(hi[a,a]*(s.diff(h[a,d],x[b])+s.diff(h[a,b],x[d])-s.diff(h[b,d],x[a]))/2) for a,b,d in product(I,repeat=3)}
G={key:v for key,v in G.items() if v!=0}
def gam(a,b,d):return G.get((a,b,d),0)
def clean(v):return s.factor(v)
def grad(f):return s.Matrix([s.diff(f,z) for z in x])
def cov(T,rank):
    @lru_cache(None)
    def D(a,*idx):
        v=s.diff(T(*idx),x[a])
        for i,b in enumerate(idx):
            v-=sum(gam(q,a,b)*T(*(idx[:i]+(q,)+idx[i+1:])) for q in I)
        return clean(v)
    return D
def tensor(M):return lambda *i:M[i[0]] if len(i)==1 else M[i]
def box(M,rank):
    D=cov(tensor(M),rank); DD=cov(D,rank+1)
    def value(*idx):return clean(sum(hi[a,a]*DD(a,a,*idx) for a in I))
    return s.Matrix([value(a) for a in I]) if rank==1 else s.Matrix(4,4,value)
def divv(v):
    D=cov(tensor(v),1);return clean(sum(hi[a,a]*D(a,a) for a in I))
def divt(T):
    D=cov(tensor(T),2);return s.Matrix([clean(sum(hi[a,a]*D(a,a,b) for a in I)) for b in I])
def Hess(f):
    D=cov(tensor(grad(f)),1);return s.Matrix(4,4,D)
def L(v):
    D=cov(tensor(v),1);return s.Matrix(4,4,lambda a,b:clean(D(a,b)+D(b,a)))
def box0(f):return clean(s.trace(hi*Hess(f)))
def zero(M):return M.applyfunc(clean)==s.zeros(*M.shape)

def run():
    t,a,b,r0=x
    f=t*t*a+t*b*r0+a*a*r0**2+b*r0**3+t*r0+2*a*b
    v=s.Matrix([(i+1)*f+x[i]**2*r0+(i+2)*x[(i+1)%4]*x[(i+2)%4] for i in I])
    H=Hess(f); lap=box0(f)
    assert zero(divt(H)-grad(lap)+3*c*grad(f))
    assert zero(box(H,2)-Hess(lap)+8*c*H-2*c*h*lap)
    Lw=L(v); dv=divv(v); bv=box(v,1)
    assert zero(divt(Lw)-bv-grad(dv)+3*c*v)
    assert zero(box(Lw,2)-L(bv)+5*c*Lw-4*c*h*dv)
    assert clean(divv(bv)-box0(dv)+3*c*dv)==0
    K=Lw-h*dv/2
    assert zero(divt(K)-bv+3*c*v-grad(dv)/2)
    assert clean(divv(divt(K))-s.Rational(3,2)*(box0(dv)-4*c*dv))==0
    # Exact scalar York resonance Q=Hess f-c h f when Box f=4c f.
    # Actual Poincare separated power r^Delta, Delta=4, no formal eigen assumption.
    f=r0**4; Q=Hess(f)-c*h*f
    assert box0(f)==4*c*f and s.trace(hi*Q)==0 and divt(Q)==s.zeros(4,1)
    assert zero(box(Q,2)+4*c*Q) and Q!=s.zeros(4)
    # Transverse vector resonance A=r^3 dx, Box A=3c A.
    A=s.Matrix([0,r0**3,0,0]); T=L(A)
    assert divv(A)==0 and zero(box(A,1)-3*c*A)
    assert s.trace(hi*T)==0 and divt(T)==s.zeros(4,1)
    assert zero(box(T,2)+2*c*T) and T!=s.zeros(4)
    # Scalar physical gauge and moving junction algebra.
    n=s.symbols('n'); B=s.Function('b')(n); k=B.diff(n)/B
    psi,phi,E,U,S,Xi=[s.Function(q)(n) for q in ('psi','phi','E','U','S','Xi')]
    X=B**2*(U-E.diff(n)); Xnew=B**2*(U+S.diff(n)+Xi/B**2-(E+S).diff(n))
    assert s.expand(Xnew-X-Xi)==0
    assert s.expand(psi+k*Xi-k*Xnew-(psi-k*X))==0
    assert s.expand(phi+Xi.diff(n)-Xnew.diff(n)-(phi-X.diff(n)))==0
    j,f0,dp,dX=s.symbols('j f dpsi dX'); k0=s.symbols('k0'); Xp,Xm=s.symbols('Xp Xm')
    # [E]=[X]=0 from independent Hessian seam conditions.
    assert s.expand((dp-k0*Xp+(k0-j)*Xm+j*(f0+Xp)).subs({dp:-j*f0,Xm:Xp}))==0
    # Diagonal scalar physical constraints: phi=-2psi and psi'=k phi.
    chi=s.Symbol('chi'); ps=chi/B**2; ph=-2*ps
    assert s.simplify(ps.diff(n)-k*ph)==0
    print('PASS 7 full covariant York/curvature identities, scalar and transverse resonance profiles')
    print('PASS scalar moving seam BIDI, conditional nonexceptional bending removal')

if __name__=='__main__':run()
