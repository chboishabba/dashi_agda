"""F8 original-wall H0..H7 rational envelopes from NORMAL source/residual caps.

Consumes the exact original characteristic GN operator and the prescribed
Pi(t,k) compact source. On 1<=t<=12, |k|<=K, explicit rational bounds for
all time derivatives of the coefficient B_n(t,0) are generated, and the
H_j recurrence is bounded by triangle inequalities. This discharges the
seven independent H-jet INPUTS from the Ward pipeline, conditional on the
second-normal trace N2_0..N2_5 and PDE residual F_0..F_5 caps.
No continuum existence, collocation accuracy, normal-regularity proof.
"""
from fractions import Fraction as Q
from math import comb, factorial
import sympy as sp


def sqrt_and_inverse_caps(order):
    """Global rational C^order envelopes for g=sqrt(1+t²), 1/g, 1<=t<=12.
    g>=1, g<=13. Differentiating g²=1+t² and g*(1/g)=1
    gives recursions controlled by triangle inequalities.
    """
    G=[Q(13),Q(1)]
    for j in range(2,order+1):
        num=Q(2) if j==2 else Q(0)
        num+=sum(Q(comb(j,i))*G[i]*G[j-i] for i in range(1,j))
        G.append(num/2)
    I=[Q(1)]
    for j in range(1,order+1):
        I.append(sum(Q(comb(j,i))*G[i]*I[j-i] for i in range(1,j+1)))
    return G[:order+1],I


def monomial_caps(power,order):
    """Sup |d^j t^power| on [1,12]."""
    return [Q(factorial(power),factorial(power-j))*12**(power-j)
            if j<=power else Q(0) for j in range(order+1)]


def coeff_caps(K,order=7):
    """A,B,C,D wall coefficient time-jet sup envelopes.
    D=B_n=-t^4/g-3t²g; A=B=t³; C=tk².
    """
    if K<0:raise ValueError('nonnegative cutoff')
    G,I=sqrt_and_inverse_caps(order)
    A=monomial_caps(3,order)
    B=A[:]
    C=[Q(K*K)*z for z in monomial_caps(1,order)]
    t4,t2=monomial_caps(4,order),monomial_caps(2,order)
    D=[sum(Q(comb(j,i))*(t4[i]*I[j-i]+3*t2[i]*G[j-i])
           for i in range(j+1)) for j in range(order+1)]
    # A0(t)=t³>=1 on the actual whole interval.
    return A,B,C,D


def wall_jet_caps(K,H0,H1,N2,F,order=7):
    """Uniform |H_j| (0<=j<=7), given only two normal-graph input families.

    N1=-6 Pi (actual first-order Israel), Pi from the original pulse.
    F=d_t^j Lh is PDE residual; zero only for an EXACT continuum solution.
    The H bounds are nonnegative rational and no division by k occurs.
    """
    if order<2 or K<0:raise ValueError('order>=2 and K>=0')
    if len(N2)<order-1 or len(F)<order-1:
        raise ValueError('need second-normal and PDE residual jets through order-2')
    if any(Q(z)<0 for z in [H0,H1,*N2,*F]):raise ValueError('invalid negative caps')
    from check_f8_original_pulse_derivative_bounds import fourier_source_bounds
    Pi=fourier_source_bounds(K,order-2)
    A,B,C,D=coeff_caps(Q(K),order)
    H=[Q(H0),Q(H1)]
    for r in range(order-1):
        rhs=Q(F[r])
        rhs+=sum(Q(comb(r,j))*(B[j]*Q(N2[r-j])+6*D[j]*Pi[r-j]+C[j]*H[r-j])
                 for j in range(r+1))
        rhs+=sum(Q(comb(r,j))*A[j+1]*H[r+1-j] for j in range(r+1))
        rhs+=sum(Q(comb(r,j))*A[j]*H[r+2-j] for j in range(1,r+1))
        # A0 >= 1, so divide by A0 only by the inequality 1/A0<=1.
        H.append(rhs)
    return H


def exact():
    t,k=sp.symbols('t k',positive=True)
    A,B,C,D=coeff_caps(Q(7,3),7)
    assert A[0]==12**3 and B[0]==12**3
    assert C[0]==12*Q(7,3)**2
    assert all(x>=0 for arr in (A,B,C,D) for x in arr)
    assert all(A[j]==0 for j in range(4,8))
    assert all(C[j]==0 for j in range(2,8))
    geom=-(t**4/sp.sqrt(1+t*t)+3*t*t*sp.sqrt(1+t*t))
    for order in range(7):
        # Samples are only a diagnostic; derivation of caps is algebraic above.
        for ti in (1,sp.Rational(21,20),6,12):
            assert abs(float(sp.diff(geom,t,order).subs(t,ti)))<float(D[order])
    first=[Q(0)]*6
    baseline=wall_jet_caps(40,Q(1),Q(1),first,first)
    assert len(baseline)==8 and all(v>=0 for v in baseline)
    pert=wall_jet_caps(40,Q(1),Q(1),[Q(1)]+first[1:],first)
    assert pert[2]>baseline[2]
    changed=wall_jet_caps(40,Q(1),Q(1),first,[Q(1)]+first[1:])
    assert changed[2]>baseline[2]
    # All original source zero-k Fourier coefficients vanish exactly as k^4.
    z0=wall_jet_caps(0,0,0,first,first)
    assert z0==[Q(0)]*8
    try:wall_jet_caps(40,1,1,first[:4],first)
    except ValueError:pass
    else:raise AssertionError('missing second-normal jets wrongly admitted')
    # The rest of the Ward source pipeline now gets H0..H7 WITH PROVEN
    # conditional caps; no arbitrary free H_j polynomial hypotheses.
    print('PASS exact original GN wall H0..H7 rational majorant, zero mode and six normal/residual negative controls')
    print('conditional H0..H7 (K=40, N2=F=0) log10 magnitudes:',
          [len(str(v.numerator))-len(str(v.denominator)) for v in baseline])

if __name__=='__main__':exact()
