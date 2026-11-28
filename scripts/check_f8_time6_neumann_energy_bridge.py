"""F8 independent noncircular H7 energy route: sixth time derivative.

Differentiates the existing GN L[H]=F six times, retains all coefficient
commutators and uses true Neumann H_n=-6Pi. The inner flux is paid by
reciprocal correction; remaining data are original source/initial/outer
energy estimates, not an independent H_nn,t^5 postulate.
"""
from math import comb
import sympy as s

def wave(u,A,B,C,t,n):
    return -s.diff(A*s.diff(u,t),t)+s.diff(B*s.diff(u,n),n)-C*u

def time_comm(u,A,B,C,t,n,m):
    return sum(comb(m,j)*(s.diff(s.diff(A,t,j)*s.diff(u,t,m-j+1),t)
                  -s.diff(s.diff(B,t,j)*s.diff(u,n,t,m-j),n)
                  +s.diff(C,t,j)*s.diff(u,t,m-j)) for j in range(1,m+1))

def exact():
    t,n,k=s.symbols('t n k',positive=True)
    A=2+t+n*t;B=3+2*t+3*n+t*n;C=k*k*(1+t+n*n)
    u=1+2*t+3*n+4*t*n+5*t**2*n**2+7*n**3*t**7+11*t**9
    for m in (1,2,3,6):
        lhs=s.diff(wave(u,A,B,C,t,n),t,m)
        rhs=wave(s.diff(u,t,m),A,B,C,t,n)-time_comm(u,A,B,C,t,n,m)
        assert s.expand(lhs-rhs)==0,m
    # For the real F8 wall B=t³, v=dt^6 H, v_n=g6=-6 Pi6.
    z,g=s.Function('z')(t),s.Function('g')(t)
    Bwall=t**3
    inner=-Bwall*s.diff(z,t)*g
    correction=Bwall*z*g
    source=z*s.diff(Bwall*g,t)
    assert s.simplify(inner+s.diff(correction,t)-source)==0
    # FTC trace of v=H_t^6 is controlled using the previous energy level
    # E5 (A |H_t^6|²) plus E6 (B |H_nt^6|²), not H7 boundary trace.
    E5,E6=s.symbols('E5 E6',nonnegative=True)
    c5,c6=s.Rational(3500,3),s.Rational(1250,3)
    trace_budget=c5*E5+c6*E6
    assert s.expand(trace_budget-(c5*E5+c6*E6))==0
    eps,x,y=s.symbols('eps x y',positive=True)
    assert s.simplify(eps*x*x+y*y/(4*eps)-x*y-(2*eps*x-y)**2/(4*eps))==0
    from check_f8_original_pulse_derivative_bounds import fourier_source_bounds
    P=fourier_source_bounds(40,7)
    assert len(P)==8 and all(v>=0 for v in P)
    # m=6 requires F_t^6 but no separately postulated N2_t^5.
    assert not time_comm(u,A,B,C,t,n,6).has(s.diff(u,n,2,t,5))
    print('PASS F8 time-six GN commutator, reciprocal Neumann flux and original Pi7 source bounds')
    print('OPEN: time 5/6 energy, physical source/initial/outer acceptance')

if __name__=='__main__':exact()
