"""F8 W2: exact variable-GN differentiated energy, material boundary work.

The time derivative of the actual five-dimensional wave carrier has a
commutator. Source regularity and physical Israel boundary traces still
need independent estimates; this file never substitutes these as zero.
"""
import sympy as s


def exact():
    t,n,k=s.symbols('t n k',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    A=a**3/N; B=N*a**3; C=N*a*k*k
    # Genuine F8 five-dimensional GN geometry, not frozen coefficients.
    assert s.simplify(s.diff(a,t)-N)==0
    assert s.simplify(s.diff(N,t)-(a-t*N)/(1+t*t))==0
    assert s.simplify(s.diff(a,n)+s.sqrt(1+t*t)*N)==0
    assert s.simplify(s.diff(N,n)+a/s.sqrt(1+t*t))==0
    # Background geometric coefficients are nonzero and time-dependent.
    A_t,B_t,C_t=[s.diff(v,t) for v in (A,B,C)]
    assert s.simplify(A_t/A-(3*N/a-s.diff(N,t)/N))==0
    assert s.simplify(B_t/B-(3*N/a+s.diff(N,t)/N))==0
    assert s.simplify(C_t/C-(N/a+s.diff(N,t)/N))==0
    # The F8 wall a=t,N=1 but N_t=0 only at n=0; spatial jets survive.
    wall=lambda f:s.simplify(f.subs(n,0))
    assert wall(A)==t**3 and wall(B)==t**3 and wall(C)==t*k*k
    assert wall(A_t)==3*t*t and wall(B_t)==3*t*t and wall(C_t)==k*k
    assert wall(s.diff(N,n))==-t/s.sqrt(1+t*t)
    # Exact differentiated five-dimensional radial Fourier equation.
    u=s.Function('u')(t,n)
    def L(v):
        return -s.diff(A*s.diff(v,t),t)+s.diff(B*s.diff(v,n),n)-C*v
    v=s.diff(u,t)
    source_t=s.diff(L(u),t)
    comm=s.diff(A_t*s.diff(u,t),t)-s.diff(B_t*s.diff(u,n),n)+C_t*u
    assert s.simplify(s.expand(L(v)-source_t-comm))==0
    assert comm!=0
    # Explicit boundary normal derivative and higher time-jet work.
    f,j=[s.Function(x)(t) for x in ('f','j')]
    Zn=(k*k*f/t**2-j)/3
    assert s.simplify(s.diff(Zn,t)-(k*k*(s.diff(f,t)-2*f/t)/t**2-s.diff(j,t))/3)==0
    Z=s.Function('Z')(t)
    Cb=(t*k*k*f/3-t**3*j/3)*Z
    assert s.simplify(-t**3*s.diff(Z,t)*Zn+s.diff(Cb,t)
        -s.diff(t*k*k*f/3-t**3*j/3,t)*Z)==0
    # The first differentiated boundary correction requires true f_t and j_t.
    dCb=s.diff(Cb,t)
    assert dCb.has(s.diff(f,t)) and dCb.has(s.diff(j,t))
    # Reverse solve on the compatible k!=0 sheet; no new pressure law.
    G,M=[s.Function(x)(t) for x in ('G','M')]
    Q=G+M/(s.I*k)+j/3
    fon=-3*t*t*(G+M/(s.I*k))/k**2
    assert s.simplify(Cb.subs(f,fon)+t**3*Z*Q)==0
    assert s.simplify(dCb.subs({s.diff(f,t):s.diff(fon,t),f:fon})+s.diff(t**3*Z*Q,t))==0
    # Real/Hermitian two-level interface: derivative of corrected source.
    z0,z1,q0,q1=s.symbols('z0 z1 q0 q1',real=True)
    assert s.expand((z0*q1+z1*q0)-(z0*q0+z1*q1)-(z0-z1)*(q1-q0))==0
    print('PASS F8 variable-coefficient GN differentiated wave and Israel source-time-jet identities')

if __name__=='__main__':exact()
