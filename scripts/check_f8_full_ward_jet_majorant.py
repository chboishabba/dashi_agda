"""Conditional C6 original F8 Fourier Ward source-jet bounds.

Given independently certified suprema H_j and A2_j for the existing
finite-band original histories, pay all temporal T,C,R derivatives using
real Pi_j bounds and source-owned background coefficients. This is not
an assertion that H_j or A2_j already have such certificates.
"""
from fractions import Fraction as F
from math import comb, factorial
import sympy as s
from check_f8_original_pulse_derivative_bounds import fourier_source_bounds


def product(x,y,n):
    return sum(F(comb(n,j))*x[j]*y[n-j] for j in range(n+1))


def product_levels(x,y,order):
    return [product(x,y,n) for n in range(order+1)]


def background_levels(order):
    """Safe time derivatives on the entire t in [1,12] GN wall.
    w=1/(12t^4), b=1/t, K=1/(3t sqrt(1+t²))-w.
    Use g=sqrt(1+t²) in [1,13], g>=1, |g'|<=1.
    """
    b=[F(factorial(j)) for j in range(order+1)]
    w=[F(factorial(j+3),72) for j in range(order+1)]
    g=[F(13),F(1)]
    for n in range(2,order+1):
        rhs=F(2) if n==2 else F(0)
        g.append((rhs+sum(comb(n,j)*g[j]*g[n-j] for j in range(1,n)))/2)
    v=[F(1)] # reciprocal g<=1
    for n in range(1,order+1):
        v.append(sum(F(comb(n,j))*g[j]*v[n-j] for j in range(1,n+1)))
    K=[sum(F(comb(n,j))*b[j]*v[n-j] for j in range(n+1))/3+w[n]
       for n in range(order+1)]
    return b,w,K


def ward_majorant(cutoff,H,A2,mu,order=6):
    """Return upper bounds for Frobenius T,C and norm-four Ward R.

    H[j]: uniform Frobenius first-order TT history derivative for |p|<=K.
    A2[j]: uniform scalar controller derivative for |p|<=2K.
    mu: nonnegative actual material shear coefficient |mu*S|.
    The amplitude coefficient belongs to the original perturbative source.
    The integrals use p in the K-ball, (2pi)^-3 integral <=K^3/54.
    All term multipliers intentionally dominate exact componentwise
    Hilbert-Schmidt bounds and the physical spatial derivative k/t.
    """
    K=F(cutoff); M=F(mu)
    if K<=0 or M<0:raise ValueError('positive cutoff and nonnegative shear')
    if len(H)<order+2 or len(A2)<order+1:
        raise ValueError('need H through order+1 and A2 through order')
    H=[F(v) for v in H];A2=[F(v) for v in A2]
    if min(H+A2)<0:raise ValueError('nonnegative jet envelopes')
    P=fourier_source_bounds(K,order+1)
    b,w,clock=background_levels(order)
    volume=K**3/54  # since pi²>9.
    HH=product_levels(H,H,order)
    HP=product_levels(H,P,order)
    AP=product_levels(A2,P,order)
    wHH=product_levels(w,HH,order)
    # T,C coefficient caps allow trace, isotropic, anisotropic and
    # controller terms; the elastic linear H is not a convolution.
    stress=[volume*20*(wHH[n]+HP[n]+AP[n])+3*M*H[n]
            for n in range(order+1)]
    # Original temporal Ward includes K H H_t, H Pi_t and b H Pi.
    Ht=H[1:];Pt=P[1:]
    KHt=product_levels(clock,product_levels(H,Ht,order),order)
    HPt=product_levels(H,Pt,order)
    bHP=product_levels(b,HP,order)
    temporal=[volume*(KHt[n]+HPt[n]+bHP[n]) for n in range(order+1)]
    # Spatial Ward is at most first tangential derivative of the three
    # bounded products (frequencies K,K,2K) or elastic H (frequency K).
    spatial=[K*(20*volume*(product(b,wHH,n)+product(b,HP,n)
                           +product(b,AP,n))+3*M*product(b,H,n))
             for n in range(order+1)]
    return {'stress_israel':stress,'ward_temporal':temporal,
            'ward_spatial':spatial,'prescribed_Pi':P,
            'fourier_volume':volume}


def exact():
    n=6
    x=s.symbols('x')
    f=1+x+2*x*x+x**3
    g=2+3*x+x*x
    Fjets=[s.diff(f,x,j).subs(x,0) for j in range(n+1)]
    Gjets=[s.diff(g,x,j).subs(x,0) for j in range(n+1)]
    for j in range(n+1):
        assert product(Fjets,Gjets,j)==s.diff(f*g,x,j).subs(x,0)
    b,w,c=background_levels(7)
    t=s.symbols('t',positive=True)
    assert s.simplify(1/(3*t*s.sqrt(1+t*t))-1/(12*t**4)-
                      (t**-2/(3*s.sqrt(1+t**-2))-t**-4/12))==0
    for j in range(8):
        assert b[j]>=0 and w[j]>=0 and c[j]>=0
    H=[F(2**j) for j in range(8)]
    A2=[F(3**j) for j in range(7)]
    r=ward_majorant(40,H,A2,5,n)
    assert len(r['stress_israel'])==7
    assert len(r['ward_temporal'])==7
    assert len(r['ward_spatial'])==7
    assert all(all(z>0 for z in r[key]) for key in
               ('stress_israel','ward_temporal','ward_spatial'))
    # The actual prescribed Pi_j is now certified, but these synthetic
    # history caps H_j,A2_j are NOT asserted for the real evolution.
    assert r['fourier_volume']==F(40**3,54)
    # The maximum stress support is 3K, source k=0 has no division.
    assert 2*40+40==120 and 40+40==80
    print('PASS exact Ward stress/Israel/R0/Ri C6 Leibniz envelopes and K/2K/3K support')
    print('sample synthetic H/A2 bound at j=5:',
          [f'{float(r[key][5]):.3e}' for key in
           ('stress_israel','ward_temporal','ward_spatial')])

if __name__=='__main__':exact()
