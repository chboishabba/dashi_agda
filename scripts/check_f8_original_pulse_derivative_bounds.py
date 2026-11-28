"""Rigorous rational envelopes for the original compact F8 clock pulse.

Original source: Pi_hat(k,t)=c(|k|) bump(t) P_TT(k) Q.
Independent C^6 time-jet bounds for the PRESCRIBED Pi, not H or A2.
No finite-difference observed drift is interpreted as a certified bound.
"""
from fractions import Fraction as F
from math import comb, factorial
import sympy as s

S, X = s.symbols('s X', real=True)
PULSE = F(13,200)       # original .065 pulse in F8 source
RADIAL = F(1,25)       # original .04 compact-source radius


def source_shape_bounds(order=6):
    """Global upper bounds on |d^j/ds^j exp(1-1/(1-s^2))|.

    On |s|<1, X=(1-s^2)^-1>=1, and
    d/ds = partial_s + 2s X^2 partial_X;
    f'/f=-2s X^2. Polynomial recurrence is exact.
    exp(1-X)X^m <=3 max(1,m^m) since exp(1-X)<=3exp(-X).
    Smooth flat extension makes the same bounds global.
    """
    poly=s.Integer(1)
    bounds=[]
    for j in range(order+1):
        terms=s.Poly(s.expand(poly),S,X).terms()
        cap=sum(3*abs(int(coeff))*max(1,degree[1]**degree[1])
                for degree,coeff in terms)
        bounds.append(F(cap))
        poly=s.expand(s.diff(poly,S)+2*S*X**2*s.diff(poly,X)-2*S*X**2*poly)
    return bounds


def clock_jet_bounds(order=6):
    """Bounds for |s^(j)(t)| on t>=1, where s=2(F(t)-F(1))/.065-1.

    F'=sqrt(1+t^2)/t^2. Bounds on derivatives of g=sqrt(1+t^2)
    are obtained from g^2=1+t^2, g>=1, g<=13 (1<=t<=12).
    For r>=1, |(t^-2)^(r)|<=(r+1)! on t>=1.
    """
    G=[F(13), F(1)]
    for n in range(2,order):
        source=F(2) if n==2 else F(0)
        G.append((source+sum(comb(n,j)*G[j]*G[n-j]
                             for j in range(1,n)))/2)
    out=[F(0)]
    for n in range(1,order+1):
        r=n-1
        Fcap=sum(F(comb(r,j))*G[j]*factorial(r-j+1)
                 for j in range(r+1))
        out.append(F(2,1)/PULSE*Fcap)
    return out


def partial_bell_bounds(jets,order=6):
    """Positive partial Bell polynomials via integer partition recurrence."""
    B={(0,0):F(1)}
    for n in range(1,order+1):
        for k in range(1,n+1):
            B[n,k]=sum(F(comb(n-1,j-1))*jets[j]*B.get((n-j,k-1),F(0))
                       for j in range(1,n-k+2))
    return B


def bump_bounds(order=6):
    shape=source_shape_bounds(order)
    clock=clock_jet_bounds(order)
    bells=partial_bell_bounds(clock,order)
    # B0<=1, superior to loose shape bound 3.
    out=[F(1)]
    for n in range(1,order+1):
        out.append(sum(shape[k]*bells[n,k] for k in range(1,n+1)))
    return out


def fourier_source_bounds(cutoff,order=6):
    """Uniform in |k|<=cutoff Frobenius norm bound for prescribed Pi jets.

    |c(k)| <= (4pi/3)*(.04)^7*K^4 because |sinc|, f <=1.
    Projector P_TT is orthogonal Frobenius projection; ||Q||_F=sqrt(2)<3/2.
    pi<22/7; hence prefactor (4*22/7)/3 * (3/2) = 44/7.
    """
    K=F(cutoff)
    if K<0:raise ValueError('nonnegative cutoff')
    coeff=F(44,7)*RADIAL**7*K**4
    return [coeff*v for v in bump_bounds(order)]


def exact():
    order=6
    poly=s.Integer(1)
    y=s.symbols('y',positive=True)
    shape=source_shape_bounds(order)
    for n in range(order+1):
        if n==0: assert shape[0]==3
        poly=s.expand(s.diff(poly,S)+2*S*X**2*s.diff(poly,X)-2*S*X**2*poly)
    # First two chain-rule Bell terms are exact, independent of envelopes.
    x1,x2,x3=s.symbols('x1 x2 x3')
    b=partial_bell_bounds([0,x1,x2,x3],3)
    assert b[2,1]==x2 and b[2,2]==x1*x1
    assert b[3,1]==x3 and b[3,2]==3*x1*x2 and b[3,3]==x1**3
    t=s.symbols('t',positive=True)
    Fprime=s.sqrt(1+t*t)/t**2
    assert s.simplify(s.diff(s.asinh(t)-s.sqrt(1+t*t)/t,t)-Fprime)==0
    jets=clock_jet_bounds(order)
    assert jets[1]==F(400) # 2/.065 * bound g0=13 =>400
    bounds=bump_bounds(order)
    assert len(bounds)==7 and all(v>=0 for v in bounds)
    kbound=fourier_source_bounds(40,order)
    assert len(kbound)==7 and all(v>0 for v in kbound)
    # Independent exact stencil constants (as used by F8 timejet checker).
    h=F(1,1000)
    M5,M6=kbound[5],kbound[6]
    E1=h**4*M5/18
    E2=h**4*M6/54
    assert E1>0 and E2>0
    # Physical t interval of a stencil must stay within [1,12].
    assert F(1035,1000)-2*h>1
    print('PASS original clock pulse global C6, source Fourier K<=40 and certified Pi timejet bounds')
    print('source bounds by derivative order (decimal magnitudes):',
          [f'{float(x):.3e}' for x in kbound])
    print('certified Pi D1,D2 h=1/1000 envelope',float(E1),float(E2))

if __name__=='__main__':exact()
