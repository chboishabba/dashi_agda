"""F8 original three-sector A2 controller: C6 jets from original H jets.

Uses the ACTUAL retarded ODE B_tt+3/t B_t+k²/t² B=F,
B(1)=B_t(1)=0 and original compact-drive support t<6/5.
No postulate of controller time derivatives; remains conditional only on
first-order metric H_j bounds (and exact original prescribed Pi_j).
"""
from fractions import Fraction as F
from math import comb, factorial
import sympy as s
from check_f8_original_pulse_derivative_bounds import fourier_source_bounds


def forcing_caps(cutoff,H,order=6,S=1):
    K=F(cutoff);drive=F(S)
    if not K>0 or drive<0:raise ValueError('positive cutoff and nonnegative drive')
    if len(H)<order+1 or any(F(x)<0 for x in H):
        raise ValueError('need actual nonnegative H_j through requested order')
    P=fourier_source_bounds(K,order)
    volume=K**3/54 # actual Fourier integration (2pi)^-3, pi²>9
    return [2*drive*volume*sum(F(comb(n,j))*F(H[j])*P[n-j]
                 for j in range(n+1)) for n in range(order+1)]


def controller_caps(cutoff,H,order=6,S=1):
    """Global on 1<=t<=12, directional A2_j envelopes.

    For each of the three SO(2) controller sectors, with wavenumber k<=2K,
    E=(B_t²+k² B²/t²)/2 has E_t=B_t F-3B_t²/t-k² B²/t³.
    Therefore |B_t(t)|<=int_1^t |F|, and |B|<=int_1^t |B_t|.
    Since source F is identically zero after t=6/5, all t<=12 satisfy
    |B_t|<=F0/5, |B|<=11F0/5. Recursively differentiate ODE, using
    |(3/t)^(j)|<=3j! and |(k²/t²)^(j)|<=4K²(j+1)!.
    The actual fixed STF Q=diag(0,1,-1) sectors m0,m1,m2 are nonnegative
    and sum to tr Q²=2, so |A2_j(k,n)|<=2 max_m |B_m^(j)|.
    """
    if order<1:raise ValueError('order>=1')
    K=F(cutoff)
    forcing=forcing_caps(K,H,max(0,order-2),S)
    sector=[F(11,5)*forcing[0], F(1,5)*forcing[0]]
    for n in range(2,order+1):
        r=n-2
        rhs=forcing[r]
        rhs+=sum(F(comb(r,j))*(3*factorial(j)*sector[n-1-j]
                         +4*K*K*factorial(j+1)*sector[n-2-j])
                 for j in range(r+1))
        sector.append(rhs)
    return [2*x for x in sector]


def exact():
    t,k=s.symbols('t k',positive=True)
    B=(t*t+t**-2-2)/8
    F0=1
    assert s.simplify(s.diff(B,t,2)+3*s.diff(B,t)/t-F0)==0
    assert B.subs(t,1)==s.diff(B,t).subs(t,1)==0
    # The independent k=0 solution obeys the same exact recurrence.
    d=[s.diff(B,t,n).subs(t,1) for n in range(8)]
    for n in range(2,8):
        r=n-2
        rhs=F(1) if r==0 else F(0)
        for j in range(r+1):
            rhs-=F(comb(r,j))*3*F((-1)**j*factorial(j))*d[n-1-j]
        assert s.simplify(d[n]-rhs)==0
    # Exact STF sector decomposition for arbitrary rational orientation.
    Q=s.diag(0,1,-1)
    n=s.Matrix([s.Rational(3,5),0,s.Rational(4,5)])
    z=(n.T*Q*n)[0];nn=Q*n
    m0=s.Rational(3,2)*z*z
    m1=2*((nn.T*nn)[0]-z*z)
    m2=s.trace(Q*Q)-m0-m1
    assert all(m>=0 for m in (m0,m1,m2))
    assert m0+m1+m2==2
    H=[F(2**j) for j in range(7)]
    A=controller_caps(40,H,6)
    assert len(A)==7 and all(v>0 for v in A)
    # No independent controller-jet postulates: only H up to order-4 needed.
    assert controller_caps(40,H[:5],6)==A
    try: controller_caps(40,H[:4],6)
    except ValueError: pass
    else: raise AssertionError('missing H4 must be rejected')
    print('PASS actual retarded controller C6 from compact source+H4, zero-mode and 3 STF sectors')
    print('conditional controller jet j0,j5,j6:',
          [f'{float(A[j]):.4e}' for j in (0,5,6)])

if __name__=='__main__':exact()
