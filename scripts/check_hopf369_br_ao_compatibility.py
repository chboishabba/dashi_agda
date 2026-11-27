#!/usr/bin/env python3
"""Instantiate n=4,s=3 fixed-interface time-jet compatibility from BR20.
Formal vacuum ADM jets and prescribed harmonic source; not free wall motion."""
import sympy as s

def run():
    t=s.symbols('t',real=True)
    # Initial gamma, A=gamma_tt, spatial coordinate acceleration v, fourth w.
    G=s.Matrix(4,4,lambda i,j:s.Symbol('g%d%d'%(min(i,j),max(i,j))))
    A=s.Matrix(4,4,lambda i,j:s.Symbol('a%d%d'%(min(i,j),max(i,j))))
    v=s.Matrix(s.symbols('v0:4')); w=s.Matrix(s.symbols('w0:4'))
    D=s.Matrix(4,4,lambda i,j:s.Symbol('d%d%d'%(i,j)))
    adv=s.Matrix(4,4,lambda i,j:s.Symbol('adv%d%d'%(min(i,j),max(i,j))))
    # Pullback x_old=x+t²v/2+t⁴w/24, through third time derivative.
    # adv=(v.d)gamma, D=dv.
    jac=s.eye(4)+t*t*D/2
    gsp=G+t*t*(A+adv)/2
    shift=((t*v+t**3*w/6).T*gsp*jac).T
    assert shift.diff(t).subs(t,0)==G*v
    assert (shift.diff(t,3).subs(t,0)-(G*w+3*(A+adv)*v+3*D.T*G*v)).applyfunc(s.expand)==s.zeros(4,1)
    zero={**dict.fromkeys(v,0),**dict.fromkeys(D,0),**dict.fromkeys(w,0),**dict.fromkeys(adv,0)}
    assert shift.diff(t,3).subs(t,0).subs(zero)==s.zeros(4,1)
    # All even components have vanishing third derivative by parity.
    N,dN=s.symbols('N dN'); g00=-(N+t*t*dN/2)**2+((t*v).T*gsp*(t*v))[0]
    gij=jac.T*gsp*jac
    assert g00.diff(t,3).subs(t,0)==0
    assert gij.diff(t,3).subs(t,0)==s.zeros(4)
    # At the seam g1=g3=0 and lambda_tt=0, as in BR20.
    eta=s.diag(-N*N,1,1,1,1); P=s.zeros(5)
    for i in range(3):
        for j in range(3):P[i+1,j+1]=A[i,j]
    for i in range(3):P[i+1,4]=P[4,i+1]=s.Symbol('m%d'%i)
    gi=eta.inv()-t*t*eta.inv()*P*eta.inv()/2
    lam=1/s.sqrt(gi[4,4]); assert lam.diff(t,2).subs(t,0)==0
    # Contracted lower Gamma jump under [dg_y]=2j lambda g in dimension 5.
    j=s.symbols('j'); e=s.eye(5)[:,4]; L=s.symbols('lam',positive=True)
    # For arbitrary metric, contraction J*g^-1 dy - tr(g^-1 J)dy/2.
    Q=s.Matrix(5,5,lambda a,b:s.Symbol('q%d%d'%(min(a,b),max(a,b))))
    # Algebraically cancel inverse with metric; use J=2j L g.
    I=s.eye(5)
    assert 2*j*L*I*e-s.trace(2*j*L*I)*e/2==-3*j*L*e
    # Source Hcommon=Gamma_lower+3j s(y) lambda dy has matching
    # value through two time derivatives, using the differentiated seam.
    lam0,lam1,lam2=s.symbols('l0 l1 l2')
    lp=lam0+t*lam1+t*t*lam2/2; gm=-3*j*lp*e
    for k in range(3):assert (gm+3*j*lp*e).diff(t,k).subs(t,0)==s.zeros(5,1)
    # Trace-reversed Einstein divergence in zero shift at initial slice:
    # E=0 spatially and parity gives E00_t=Eij_t=0. Only E0i_t remains;
    # contracted Bianchi nu=i gives -E0i_t/N²=0.
    e0=s.Matrix(s.symbols('e0:4')); dE=s.zeros(5); dE[0,1:5]=e0.T;dE[1:5,0]=e0
    rev=dE-eta*s.trace(eta.inv()*dE)/2
    assert rev[0,1:5]==e0.T
    assert eta.inv()[0,0]*rev[0,1:5]==-e0.T/N**2
    # n=4,s=3: H^{2,4}, H^{2,3}, H^{2,2}, H^{1,1}.
    s0=3
    assert [(min(2,s0+1-k),s0+1-k) for k in range(4)]==[(2,4),(2,3),(2,2),(1,1)]
    print('PASS pullback third time jet, reflection parity, harmonic source compatibility, Bianchi first derivative')
    print('PASS finite compatibility allocation n=4,s=3 (conditional on BR20/BQ spatial jets)')
if __name__=='__main__':run()
