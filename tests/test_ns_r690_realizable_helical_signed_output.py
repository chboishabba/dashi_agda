"""Physical same-source negative output-rate witness for B/R685/R690.

The actual helical projectors are H±_p u=(P_p u ± i(p×u)/|p|)/2;
the mixed cell is H+_p(u_p)×H-_q(u_q), exactly as in
NSTriadKNPeriodicHelicalFourierInfrastructure and
NSTriadKNFixedOutputMixedCommutatorDampedTangentExact.

Our original counterexample/calibration: a REAL transverse, finite-mode
unforced Navier--Stokes heat shear. This refutes pointwise nonnegativity
of individual R690 output terms, NOT global signed output sums, integrated
uniform estimates, auxiliary R823 reserves, or Clay B.
"""
from collections import defaultdict
import sympy as s

I=s.I
P1=(1,1,0); Q1=(1,-1,0); P2=(0,2,0); Q2=(2,-2,0)
K=(2,0,0)
Z=s.Matrix([0,0,1])

def neg(p): return tuple(-v for v in p)
def sq(p): return sum(v*v for v in p)
def helical(p,sign,u):
    pvec=s.Matrix(p)
    return s.simplify((u+sign*I*pvec.cross(u)/s.sqrt(sq(p)))/2)
def work(u,v): return s.simplify(2*s.re((s.conjugate(u).T*v)[0]))
def seed():
    result={P1:Z,Q1:Z,P2:Z,Q2:-Z}
    result.update({neg(p):s.conjugate(v) for p,v in list(result.items())})
    return result
def certificate(u,k):
    cells=[]
    for p,up in u.items():
        q=tuple(k[j]-p[j] for j in range(3))
        if q not in u: continue
        product=s.simplify(helical(p,1,up).cross(helical(q,-1,u[q])))
        cells.append((p,q,product,sq(p)+sq(q)))
    M=sum((v for _,_,v,_ in cells),s.zeros(3,1))
    rate=s.simplify(sum(r*work(M,v) for _,_,v,r in cells))
    output_heat=s.Rational(1,2)*sq(k)*work(M,M)
    signed=s.Rational(1,2)*sum(
        sq(tuple(p[j]-q[j] for j in range(3)))*work(M,v)
        for p,q,v,_ in cells)
    assert s.simplify(rate-output_heat-signed)==0
    return cells,M,rate,output_heat,signed

def test_unforced_real_divergence_free_helical_output_negative():
    u=seed()
    assert all(s.Matrix(p).dot(v)==0 for p,v in u.items())
    assert all(u[neg(p)]==s.conjugate(v) for p,v in u.items())
    cells,M,rate,positive,signed=certificate(u,K)
    assert len(cells)==4
    assert sorted(r for _,_,_,r in cells)==[4,4,12,12]
    assert rate==8-6*s.sqrt(2)<0
    assert s.simplify(positive-(2-s.sqrt(2)))==0
    assert s.simplify(signed-(6-5*s.sqrt(2)))==0
    assert certificate(u,neg(K))[2]==rate

def test_exact_heat_trajectory_and_finite_time_negative_integral():
    t,T=s.symbols("t T",real=True,positive=True)
    u={p:v*s.exp(-sq(p)*t) for p,v in seed().items()}
    cells,M,rate,_,_=certificate(u,K)
    self_energy=s.simplify((s.conjugate(M).T*M)[0])
    assert s.simplify(s.diff(self_energy,t)+rate)==0
    assert s.simplify(rate.subs(t,0)-(8-6*s.sqrt(2)))==0
    assert s.simplify(s.integrate(rate,(t,0,T))-
                      (self_energy.subs(t,0)-self_energy.subs(t,T)))==0
    assert s.N(s.integrate(rate,(t,0,s.Rational(1,100))))<0
    assert s.simplify(s.integrate(rate,(t,0,s.oo))-self_energy.subs(t,0))==0
    # Since every velocity has only z component and depends only on x,y,
    # (u·grad)u=0. Each Fourier coefficient solves the heat equation.

def test_single_output_not_global_sign():
    u=seed()
    outputs={tuple(p[j]+q[j] for j in range(3)) for p in u for q in u}
    total=s.simplify(sum(certificate(u,k)[2] for k in outputs if k!=(0,0,0)))
    assert total==192-16*s.sqrt(2)>0
    # A negative fixed-output work is NOT a negative global R690 work.

def test_full_R690_global_heat_endpoint_identity():
    # The SAME physical unforced heat field; full output sum includes
    # all 26 nonzero frequencies (not just the negative local k).
    t=s.symbols("t",real=True,nonnegative=True)
    u={p:v*s.exp(-sq(p)*t) for p,v in seed().items()}
    outputs={tuple(p[j]+q[j] for j in range(3)) for p in u for q in u}
    outputs.discard((0,0,0))
    assert len(outputs)==26
    total=s.simplify(sum(certificate(u,k)[2] for k in outputs))
    expected=8*(3*s.exp(24*t)+6*s.exp(20*t)
                -(3+2*s.sqrt(2))*s.exp(16*t)
                +10*s.exp(12*t)+6*s.exp(8*t)+2)*s.exp(-32*t)
    assert s.simplify(total-expected)==0
    # This is the R691 signed mixed-energy endpoint for the real
    # heat solution: every nonlinear commutator vanishes.
    mixed_initial=12-s.sqrt(2)
    assert s.simplify(s.integrate(total,(t,0,s.oo))-mixed_initial)==0
    assert s.simplify(8*s.integrate(total,(t,0,s.oo))
                      -(96-8*s.sqrt(2)))==0
    assert s.simplify(total.subs(t,0)-(192-16*s.sqrt(2)))==0
