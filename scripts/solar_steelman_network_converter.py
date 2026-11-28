"""Causal LC branch states replace standalone matching resistances.
Complex two-quadrature finite model, normalized angular frequencies 2:1.
Not the physical distributed Maxwell or single-real-field constitutive law.
"""
import sympy as S
from solar_steelman_unity import zero, rhs
from solar_steelman_hf_continuous import two_mode_hamiltonian

I=S.I

def branch(w,v):
    # Foster series branch from causal_match: L s + K/s + s/(s²+v²).
    # Reverse zero reactance against unit real reference at own carrier.
    L=2+abs(1/(v*v-w*w));K=w*w*(L+1/(v*v-w*w))
    assert L>0 and K>0
    assert S.cancel(w*L-K/w+w/(v*v-w*w))==0
    return L,K


def run():
    two_mode_hamiltonian()
    # Input series current is sqrt(2)*a; normalize its auxiliary coordinates
    # by sqrt(2). Output currents are b,d; only final load resistors dissipate.
    names=['a','c','b','d']+[f'{k}{j}' for k in ('a','b','d') for j in ('q','x','z')]
    r=S.symbols('r:13',real=True); im=S.symbols('i:13',real=True)
    X=S.Matrix([u+I*v for u,v in zip(r,im)])
    a,c,b,d=X[:4]; sr,si=S.symbols('sr si',real=True);s=sr+I*si
    raw=list(rhs(S.Matrix([a,c,b,d]),s));ff=raw+[0]*9
    metric=[1]*13; physical=[2,2,1,1]+[0]*9
    nominal=[1/S.sqrt(2)]*4+[0]*9
    for index,offset,w,v,scale in [(0,4,S.Integer(2),S.Integer(1),2),(2,7,S.Integer(1),S.Integer(2),1),(3,10,S.Integer(1),S.Integer(2),1)]:
        L,K=branch(w,v);u=X[index];q,x,z=X[offset:offset+3]
        ff[index]=(raw[index]-I*w*L*u-K*q-x)/(1+L)
        ff[offset:offset+3]=[u-I*w*q,u-v*v*z-I*w*x,x-I*w*z]
        metric[index]=1+L;metric[offset:offset+3]=[K,1,v*v]
        physical[index]=scale*(1+L);physical[offset:offset+3]=[scale*K,scale,scale*v*v]
        t=nominal[index];nominal[offset:offset+3]=[t/(I*w),I*w*t/(v*v-w*w),t/(v*v-w*w)]
    ff=S.Matrix(ff);sub=dict(zip(r+im+(sr,si),[S.re(z) for z in nominal]+[S.im(z) for z in nominal]+[1,0]))
    assert zero(ff.subs(sub))
    # Exact arbitrary-state global power ledger. Input resistor is source
    # reference radiation, not a converter/receiver dissipation term.
    balance=S.re(sum(w*S.conjugate(z)*f for w,z,f in zip(physical,X,ff)))
    refl=s-S.sqrt(2)*a;bright=(b+d)/S.sqrt(2);dark=(b-d)/S.sqrt(2)
    assert zero(balance-s*S.conjugate(s)+refl*S.conjugate(refl)+bright*S.conjugate(bright)+dark*S.conjugate(dark))
    assert zero(refl.subs(sub)) and zero(dark.subs(sub)) and zero(bright.subs(sub)-1)
    # All LC envelope states restore and physical quadrature carriers share
    # period 2pi. The HF action is fixed; two-mode rotation is independent
    # at nominal phase lock. This is not a full single-real-field PDE.
    F=S.Matrix([S.re(v).expand(complex=True) for v in ff]+[S.im(v).expand(complex=True) for v in ff])
    A=F.jacobian(r+im).subs(sub).applyfunc(S.simplify)
    G=S.diag(*(metric+metric));H=(-(G*A+A.T*G)/2).applyfunc(S.simplify)
    # Compare exactly to the original converter dissipation block.
    raw_real=S.Matrix([S.re(v).expand(complex=True) for v in raw]+[S.im(v).expand(complex=True) for v in raw])
    Ar=raw_real.jacobian(r[:4]+im[:4]).subs(sub);Hr=-(Ar+Ar.T)/2
    ids=[0,1,2,3,13,14,15,16];expected=S.zeros(26)
    for i,p in enumerate(ids):
        for j,q in enumerate(ids):expected[p,q]=Hr[i,j]
    assert H==expected and Hr.is_positive_semidefinite
    # Largest A-invariant subspace of ker H, exact rational elimination.
    N=S.Matrix.hstack(*H.nullspace());dims=[N.cols]
    while N.cols:
        constraints=H*A*N
        # Invariance refinement uses annihilator of current subspace.
        annih=N.T.nullspace()
        constraints=S.Matrix.vstack(*[v.T*A*N for v in annih])
        ns=constraints.nullspace()
        if len(ns)==N.cols:break
        if not ns:N=S.zeros(26,0)
        else:N=N*S.Matrix.hstack(*ns)
        dims.append(N.cols)
    assert N.cols==0, dims
    print('PASS exact continuous causal LC converter: incident=1 useful=1 reflection=0 dark=0')
    print('PASS weighted dissipativity and invariant-kernel elimination',dims,'rank=26/26')
    print('Conditional normalized two-quadrature branches, fixed HF action; physical source and distributed Maxwell open')
if __name__=='__main__':run()
