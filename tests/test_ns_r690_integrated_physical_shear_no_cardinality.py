"""Physical unforced shear: R689/R690 no-cardinality rate integration.

Original physical solution: u(t,x,y,z)=2 exp(-t)(cos x+cos y)e_z,
viscosity=1 on T³. Its NS nonlinear term vanishes pointwise.
The H+×H- mixed-product cell fingerprints at k=(1,1,0) are
recorded in scripts/ns_b4_literal_padding_adversary.py; this test
checks source-specific work and its integrated heat-rate identity.

NOT a proof of an arbitrary-trajectory global signed estimate or Clay B.
"""
import sympy as s

def W(u,v):
    return s.simplify(2*s.re((s.conjugate(u).T*v)[0]))

def test_exact_time_dependent_shear_rate_integral_and_zero_padding():
    t,T=s.symbols("t T",real=True,positive=True)
    base=s.exp(-2*t)
    A=base*s.Matrix([-s.I/4,-s.I/4,s.Rational(1,4)])
    B=base*s.Matrix([-s.I/4,-s.I/4,-s.Rational(1,4)])
    M=A+B
    k=(1,1,0)
    p=(1,0,0);q=(0,1,0)
    outRate=s.Rational(1,2)*sum(x*x for x in k)
    diffRate=s.Rational(1,2)*sum((p[i]-q[i])**2 for i in range(3))
    K=2*(W(M,A)+W(M,B))
    split=outRate*W(M,M)+diffRate*(W(M,A)+W(M,B))
    assert s.simplify(K-2*s.exp(-4*t))==0
    assert s.simplify(K-split)==0
    signed_R690_one_output=8*K
    assert s.simplify(
      s.integrate(signed_R690_one_output,(t,0,T))
       -4*(1-s.exp(-4*T)))==0
    # The force is zero in this exact NS solution. Thus its R685
    # commutator W(M,C)=0, tangent W(M,T)=-K, so
    # rate-lifted 0 - 8 tangent = 8 K at every t.
    assert s.simplify(0-8*(-K)-signed_R690_one_output)==0
    for n in (16,32,64):
        far=(n,0,0);other=(1-n,1,0)
        zero=s.zeros(3,1)
        rate=sum(x*x for x in far)+sum(x*x for x in other)
        assert W(M,zero)==0
        assert s.simplify(K+rate*W(M,zero)-K)==0
        # Old full-fibre count-centered covariance at this k
        # changes by (rate-2)*exp(-4t), despite no physical change.
        old=0
        count_centered=3*(-K)+(4+rate)*W(M,M)
        assert s.simplify(count_centered-(rate-2)*s.exp(-4*t))==0

def test_shear_is_unforced_NS_heat_solution():
    x,y,z,t=s.symbols("x y z t",real=True)
    u=s.Matrix([0,0,2*s.exp(-t)*(s.cos(x)+s.cos(y))])
    variables=(x,y,z)
    assert all(s.simplify(sum(u[j]*s.diff(u[i],variables[j])
               for j in range(3)))==0 for i in range(3))
    assert all(s.simplify(s.diff(u[i],t)-sum(
       s.diff(u[i],v,2) for v in variables))==0 for i in range(3))
