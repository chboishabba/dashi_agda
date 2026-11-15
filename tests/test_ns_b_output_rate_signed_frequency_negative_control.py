"""Adversarial exact signed difference-frequency check for the R685/R690 owner.

In a generic complex source-cell family, even though |p-q|²>=0,
the Hermitian WORK W(M, sum |p-q|² A_pq) need not be nonnegative.
This is an algebraic carrier witness, not a proof that its values arise
from the source-selected physical helical velocity of R685.
"""
import sympy as S

def test_signed_frequency_work_can_be_negative_but_full_rate_identity_exact():
    k=(2,0,0)
    nu=S.Rational(3,2)
    cells=[
       ((1,0,0),(1,0,0),S.Matrix([1,0,0])),
       ((20,0,0),(-18,0,0),S.Matrix([-S.Rational(3,4),0,0])),
    ]
    M=sum((v for _,_,v in cells),S.zeros(3,1))
    def W(v):
        return S.simplify(2*S.re((S.conjugate(M).T*v)[0]))
    weighted=sum(nu*(sum(x*x for x in p)+sum(x*x for x in q))*W(v)
                 for p,q,v in cells)
    common=nu*S.Rational(1,2)*sum(x*x for x in k)*W(M)
    centered=nu*S.Rational(1,2)*sum(
        sum((p[i]-q[i])**2 for i in range(3))*W(v)
        for p,q,v in cells)
    assert S.simplify(weighted-common-centered)==0
    assert common>0
    assert centered<0
    assert weighted<0
    for n in (40,100,1000):
        p=(n,0,0);q=(2-n,0,0)
        assert tuple(p[i]+q[i] for i in range(3))==k
        z=S.zeros(3,1)
        assert W(z)==0
        assert weighted+nu*(sum(x*x for x in p)+sum(x*x for x in q))*W(z)==weighted

def test_physical_shear_centering_fixed_despite_original_covariance_divergence():
    M=S.Matrix([-S.I/2,-S.I/2,0])
    A=S.Matrix([-S.I/4,-S.I/4,S.Rational(1,4)])
    B=S.Matrix([-S.I/4,-S.I/4,-S.Rational(1,4)])
    def W(v):return S.simplify(2*S.re((S.conjugate(M).T*v)[0]))
    rate=2
    outputHeat=1
    centered=1
    assert rate*(W(A)+W(B))==outputHeat*W(M)+centered*(W(A)+W(B))==2
    for n in (16,32,64):
        p=(n,0,0);q=(1-n,1,0)
        r=sum(x*x for x in p)+sum(x*x for x in q)
        assert r==2*n*n-2*n+2
        assert W(S.zeros(3,1))==0
        assert 2*(W(A)+W(B))==2
        assert r-2>0 # only the literal full-fibre mean changes
