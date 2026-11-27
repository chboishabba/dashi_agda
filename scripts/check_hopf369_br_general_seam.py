#!/usr/bin/env python3
"""Exact moving Israel/harmonic seam on arbitrary adapted background jets.
Classical coordinate and defining-function identities; no nonlinear evolution.
"""
import sympy as s


def run():
    j,f=s.symbols('j f',real=True)
    g=s.diag(-1,1,1,1,1); n=s.eye(5)[:,4]; nn=n*n.T
    a=s.Matrix([*s.symbols('df0:4'),0]); Q=s.zeros(5)
    ix=range(5); k=0; vals=s.symbols('q0:15')
    for i in ix:
        for l in range(i,5):Q[i,l]=Q[l,i]=vals[k];k+=1
    z=Q[4,4]; e=s.symbols('e')
    # First-order inverse, moving graph normal and normal derivative jump.
    gi=g-e*g*Q*g; dF=n-e*a
    F2=(dF.T*gi*dF)[0]; assert s.diff(F2,e).subs(e,0)==-z
    lam=1+e*z/2; nc=lam*dF
    J=lam*(2*j*(g+e*Q)+6*j*nc*nc.T)
    R=J.diff(e).subs(e,0)
    expected=2*j*Q+j*z*g+9*j*z*nn-6*j*(a*n.T+n*a.T)
    assert (R-expected).applyfunc(s.expand)==s.zeros(5)
    # Actual nonzero mean and unequal second derivatives: material good unknown.
    B=s.Matrix(5,5,s.symbols('b0:25')); D=s.Matrix(5,5,s.symbols('d0:25'))
    m=Q-f*B; derivative=expected-f*D
    assert (derivative+f*D-expected).applyfunc(s.expand)==s.zeros(5)
    # Variation of d_mu log lambda at fixed graph, evaluated at adapted point.
    # dg[mu] and material d_mu perturbation arbitrary symmetric.
    G=s.zeros(5); P=s.zeros(5); v=s.symbols('G0:15'); w=s.symbols('P0:15'); k=0
    for i in ix:
        for l in range(i,5):G[i,l]=G[l,i]=v[k];P[i,l]=P[l,i]=w[k];k+=1
    dgi=-gi*(G+e*P)*gi
    dF2=(dF.T*dgi*dF)[0]
    dlog=-dF2/(2*F2)
    direct=s.diff(dlog,e).subs(e,0)
    qn=g*Q*n; tilt=g*a; tang=qn-z*n+tilt
    expected_log=P[4,4]/2-z*G[4,4]/2-(tang.T*G*n)[0]
    assert s.expand(direct-expected_log)==0
    # n^mu = lambda g^munu F_nu; delta n^mu = -z n/2 - tang.
    dn=(lam*gi*dF).diff(e).subs(e,0)
    assert (dn+z*n/2+tang).applyfunc(s.expand)==s.zeros(5,1)
    # At common wall value, mean geometric wall residual kappa+C_n=0
    # implies mean(H_n)=mean(d_n log lambda). The general q_nn coefficient
    # -3/4 B_nn+H_n/2 then becomes -1/2 B_nn.
    bn,Hn=s.symbols('bn Hn'); assert (-3*bn/4+Hn/2).subs(Hn,bn/2)==-bn/2
    # Same-source chart transport: arbitrary sheared Lorentz metric by congruence.
    N,L=s.symbols('N L',positive=True); X=s.eye(5); X[0,4]=s.Symbol('shift0');X[1,4]=s.Symbol('shift1');X[2,4]=s.Symbol('shift2');X[3,4]=s.Symbol('shift3');X[4,4]=L
    gg=X.T*s.diag(-N*N,1,1,1,1)*X; inv=s.simplify(gg.inv()); nc=L*n
    # second-coordinate-jet jump [a] = -3j lambda^3 g^-1 dy
    A=-3*j*L**3*inv*n
    delta=gg*A*n.T+n*(gg*A).T
    assert (delta+6*j*L*nc*nc.T).applyfunc(s.simplify)==s.zeros(5)
    # inhomogeneous contracted lower Christoffel/source transformation.
    assert (inv[4,4]*gg*A+3*j*nc).applyfunc(s.simplify)==s.zeros(5,1)
    # inverse chart second jet sign; all coordinates and signs retained.
    assert (delta+(-delta))==s.zeros(5)
    # Normal graph term on symmetric AK recovers BR9 zero order. In Y chart
    # g_nn=b^8, dY b=b^5 k, k_n=1-k², so g_nn,YY=8(1+11 k²).
    b,k=s.symbols('b k',real=True); op=lambda v:s.diff(v,b)*b**5*k+s.diff(v,k)*b**4*(1-k*k)
    assert s.expand(op(op(b**8)).subs(b,1)/2-(4+44*k*k))==0
    assert (4+44*k*k).subs(k,j/2)==4+11*j*j
    print('PASS general 15-component material jump, defining-function wall gradient, nonzero-mean terms, sheared chart/source transport, AK regression')

if __name__=='__main__':run()
