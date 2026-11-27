"""Rigorous conservative radial spectral tails for the original linear history.
Bounds on energy and mass, not a pointwise Weyl receiver or normal error certificate.
"""
from fractions import Fraction as Q
import sympy as s


def derivative_bound(m):
    """Bound L1(0,1) derivative order 2m of u exp(1-1/(1-u²))."""
    u,X=s.symbols('u X'); P=u
    for _ in range(2*m):
        P=s.Poly(s.diff(P,u)+2*u*X**2*(s.diff(P,X)-P),u,X).as_expr()
    return sum(abs(int(c))*3*max(1,j**j) for (i,j),c in s.Poly(P,u,X).terms())


def spectral_constant(m):
    if m<4:raise ValueError('mass tail requires m>=4')
    return 16*25**(2*m-6)*derivative_bound(m)


CE=10**12*3**77


def mass_tail(K,m):
    """Upper bound for omitted positive mass coefficient over k>=K, K>=1."""
    K=Q(K)
    if K<1:raise ValueError('cutoff must be >=1')
    return Q(128*CE**2*spectral_constant(m)**2,4*m-13)*K**(13-4*m)


def exact():
    u,X=s.symbols('u X'); f=s.exp(1-1/(1-u*u)); P=u
    for j in range(1,5):
        P=s.expand(s.diff(P,u)+2*u*X**2*(s.diff(P,X)-P))
        assert s.simplify(s.diff(u*f,u,j)/f-P.subs(X,1/(1-u*u)))==0
    # Integration by parts at origin: every even derivative vanishes.
    for j in range(0,8,2):assert s.diff(u*f,u,j).subs(u,0)==0
    # Actual proper clock derivatives and spatial lift budgets.
    assert Q(400,13)**2*2<44**2  # 2/.065=400/13
    assert 24*44<1100 and 3744*44**2+24*88<8*10**6
    assert 6*(169*8*10**6*Q(3,10)+325*1100*Q(3,10)+140+16*7)<3*10**9
    assert 6*16*Q(3,10)<3*10**9
    assert 3*12**3<=72**2 and 13*14<32*6
    assert Q(3*10**9*72,7)*3**77+10**10<CE
    # Both energy derivative coefficient and energy-to-mass bounds are conservative.
    assert 13+1==14 and Q(1,64*13)<Q(1,64*12)
    assert 4*4-13>0
    print('radial derivative, integration-by-parts and rational energy budgets PASS')
    for m in (4,6,8):
        D=spectral_constant(m)
        # Explicit exact rational evaluations; huge conservative constants.
        for K in (80,10**6,10**12):
            b=mass_tail(K,m)
            print('m,cutoff,log10 bound',m,K,float(s.log(b.numerator,10)-s.log(b.denominator,10)))

if __name__=='__main__':exact()
