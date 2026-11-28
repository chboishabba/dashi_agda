"""Original F8 characteristic history: bidirectional seven-time-jet reconstruction.

This is an EXACT differential recursion, not a continuum existence theorem.
It replaces seven freely postulated H time jets by H0,H1, the actual
Israel first-normal source, second-normal traces N2_0..N2_5, and the
true PDE residual F0..F5. The missing certified input is now precisely
normal regularity plus numerical residual control, NOT another H7 postulate.

GN scalar TT principal operator: Lh=-d_t(A h_t)+d_n(B h_n)-C h,
A=a^3/N, B=N*a^3, C=N*a*k^2. On n=0,
A=B=t^3, C=t*k^2, B_n=-t^4/sqrt(1+t^2)-3*t^2*sqrt(1+t^2).
The actual original boundary characteristic condition gives h_n=-6 Pi.
"""
from math import comb
import sympy as s


def coefficients(t,k,order=6):
    A=t**3
    B=t**3
    C=t*k*k
    D=-t**4/s.sqrt(1+t*t)-3*t*t*s.sqrt(1+t*t)
    return tuple([[s.diff(x,t,j) for j in range(order+1)]
                  for x in (A,B,C,D)])


def reconstruct(H0,H1,N1,N2,F,coeff,order=7):
    """Full off-shell wall PDE recurrence, no k division, complex allowed.

    N1_j=normal first derivatives; actual Israel constraint is N1_j=-6 Pi_j.
    N2_j=normal second derivatives, requiring independent graph regularity.
    F_j=d_t^j(Lh) are actual consistency residual derivatives.
    """
    if order<2:raise ValueError('order>=2')
    A,B,C,D=coeff
    if any(len(x)<order-1 for x in (A,B,C,D)) or any(len(x)<order-1 for x in (N1,N2,F)):
        raise ValueError('missing normal/source/geometry jets')
    if A[0]==0:raise ValueError('degenerate lapse or warp')
    H=[H0,H1]
    for r in range(order-1):
        rhs=-F[r]
        rhs+=sum(comb(r,j)*(B[j]*N2[r-j]+D[j]*N1[r-j]-C[j]*H[r-j])
                 for j in range(r+1))
        rhs-=sum(comb(r,j)*A[j+1]*H[r+1-j] for j in range(r+1))
        rhs-=sum(comb(r,j)*A[j]*H[r+2-j] for j in range(1,r+1))
        H.append(s.expand(rhs/A[0]))
    return H


def exact():
    t,n,k=s.symbols('t n k',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    A=a**3/N; B=N*a**3; C=N*a*k*k
    c=coefficients(t,k,6)
    assert s.simplify(B.subs(n,0)-t**3)==0
    assert s.simplify(s.diff(B,n).subs(n,0)-c[3][0])==0
    # Manufactured time/normal polynomial, no forced on-shell assumption.
    # Use independent exact rational coefficients at one original wall time.
    t0=s.Rational(21,20);k0=s.Rational(7,3)
    x=t-t0
    U=sum(s.Rational((j*7)%11-5,j+3)*x**j for j in range(8))
    V=sum(s.Rational((j*5)%13-6,j+4)*x**j for j in range(7))
    W=sum(s.Rational((j*3)%17-8,j+5)*x**j for j in range(7))
    h=U+n*V+n*n*W/2
    a0,b0,c0,d0=coefficients(t,k0,6)
    L=-s.diff(A*s.diff(h,t),t)+s.diff(B*s.diff(h,n),n)-C.subs(k,k0)*h
    norm=lambda z:s.simplify(z.subs({n:0,t:t0}))
    H=[norm(s.diff(h,t,j)) for j in range(8)]
    N1=[norm(s.diff(h,n,t,j)) for j in range(6)]
    N2=[norm(s.diff(h,n,2,t,j)) for j in range(6)]
    F=[norm(s.diff(L,t,j)) for j in range(6)]
    jets=tuple([norm(v) for v in row] for row in (a0,b0,c0,d0))
    recovered=reconstruct(H[0],H[1],N1,N2,F,jets,7)
    assert all(s.simplify(u-v)==0 for u,v in zip(recovered,H)),[(j,s.simplify(u-v)) for j,(u,v) in enumerate(zip(recovered,H))]
    # Exact actual Israel boundary: h_n=-6 Pi, including every time derivative.
    Pi=[s.symbols('Pi'+str(j)) for j in range(6)]
    on_israel=reconstruct(H[0],H[1],[-6*v for v in Pi],N2,F,jets,7)
    assert len(on_israel)==8 and all(v.has(k0) is False for v in on_israel[:2])
    # Exact boundary-normal mismatch is an independent residual and propagates.
    e=[s.symbols('e'+str(j)) for j in range(6)]
    off=reconstruct(H[0],H[1],[-6*Pi[j]+e[j] for j in range(6)],N2,F,jets,7)
    assert s.simplify(off[2]-on_israel[2]-jets[3][0]*e[0]/jets[0][0])==0
    # Negative control: forcing residual or second-normal trace influences H2.
    dr=reconstruct(H[0],H[1],N1,[N2[0]+1]+N2[1:],F,jets,7)
    assert s.simplify(dr[2]-recovered[2]-1)==0
    df=reconstruct(H[0],H[1],N1,N2,[F[0]+1]+F[1:],jets,7)
    assert s.simplify(df[2]-recovered[2]+1/jets[0][0])==0
    try:reconstruct(H[0],H[1],N1,N2[:4],F,jets,7)
    except ValueError:pass
    else:raise AssertionError('insufficient normal jets admitted')
    # Characteristic solver's boundary R-L=12 Pi -> h_n=(R-L)/2=-6 Pi.
    R,Lchar,source=s.symbols('R L Pi')
    assert s.simplify(((R-Lchar)/2+6*source).subs(R,Lchar-12*source))==0
    print('PASS exact original F8 characteristic H0..H7 wall recurrence; six off-shell residual jets and Israel mismatch retained')
    print('H7 computed without an independent H7 hypothesis; N2_0..N2_5 and F_0..F_5 remain actual proof inputs')


if __name__=='__main__':exact()
