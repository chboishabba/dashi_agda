"""Regression for the literal noncore/core B4 cutoff-padding no-go.

Two active ordered physical cells remain unchanged at every N, while
zero-amplitude high-high physical incidences alter centering moments.
Failure is *not* automatically a counterexample to a payment with an
unconstrained N-dependent localED input.
"""
import importlib.util
from pathlib import Path
from fractions import Fraction

P=Path(__file__).resolve().parents[1]/"scripts/ns_b4_literal_padding_adversary.py"
spec=importlib.util.spec_from_file_location("ns_b4_padding",P)
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

def test_authoritative_output_and_exact_two_core_cells():
    assert module.K==(1,1,0)
    assert module.region(module.P,module.Q)=="core"
    assert module.region(module.Q,module.P)=="core"
    assert module.region((10,0,0),(-9,1,0))=="noncore"

def test_literal_b4_padding_exact_certificates():
    results={n:module.certificate(n) for n in (4,8,9,16,24,36,40)}
    assert results[4]["signed_defect"]=="0"
    assert results[8]["signed_defect"]=="0"
    for n in (9,16,24,36,40):
        assert results[n]["core_rows"]==5474
        assert results[n]["literal_core_companion"]=="1345859672"
    assert results[9]["signed_defect"]=="185520"
    assert results[16]["signed_defect"]=="16776416"
    assert results[24]["signed_defect"]=="130871520"
    assert results[36]["signed_defect"]=="988633056"
    assert results[40]["signed_defect"]=="1671172320"
    assert results[36]["defect_exceeds_half_companion"]
    assert results[40]["defect_exceeds_half_companion"]

def test_no_renormalization_by_ignoring_zero_cells():
    n8=module.certificate(16)
    n16=module.certificate(40)
    assert n8["noncore_zero_amplitude_rows"]==28318
    assert n16["noncore_zero_amplitude_rows"]==512926
    assert Fraction(n16["signed_defect"])>Fraction(n8["signed_defect"])
    assert n16["literal_core_companion"]==n8["literal_core_companion"]

def test_unbounded_positive_subfamily_of_zero_amplitude_rows():
    # For each integer m>=10, p=(m,0,0), q=(1-m,1,0) is a noncore
    # row when cutoff N>=m. Its rate excess is exactly 2*m*(m-1).
    for m in (10,11,20,30,50):
        p=(m,0,0)
        q=(1-m,1,0)
        assert module.region(p,q)=="noncore"
        assert sum(x*x for x in p+q)-2==2*m*(m-1)
    assert sum(2*m*(m-1) for m in range(10,41)) <= int(
        module.certificate(40)["signed_defect"])


def test_selected_shear_is_genuine_unforced_solution_and_modal_R440_is_invariant():
    # u(t)=2*exp(-t)*(cos(x)+cos(y))*e_z is divergence-free.
    # u·grad u = u_z ∂_z u = 0; -Delta u0 = u0.
    # The two active H+ x H- cells have A,B as below;
    # this is exact Gaussian-rational arithmetic with denominator 4.
    from fractions import Fraction as F
    # Complex stored as pairs (real,imag), all components exact.
    A=((F(0),F(-1,4)),(F(0),F(-1,4)),(F(1,4),F(0)))
    B=((F(0),F(-1,4)),(F(0),F(-1,4)),(F(-1,4),F(0)))
    M=tuple((a[0]+b[0],a[1]+b[1]) for a,b in zip(A,B))
    assert M==((F(0),F(-1,2)),(F(0),F(-1,2)),(F(0),F(0)))
    normM=sum(z[0]**2+z[1]**2 for z in M)
    assert normM==F(1,2)
    rweighted=tuple((2*z[0],2*z[1]) for z in M)
    # Unlike full-fibre covariance, modal R440 weighted amplitude stays 2*M.
    assert all(rweighted[j]==(2*M[j][0],2*M[j][1]) for j in range(3))
    # W(M,2M)=2*Re(conj(M)·(2M))=2.
    assert 2 * 2 * normM == 2
    # Output k=(1,1,0) has |k|²=2, so the true centered modal rate is ZERO.
    assert all(rweighted[j]==(sum(x*x for x in module.K)*M[j][0],
                             sum(x*x for x in module.K)*M[j][1])
               for j in range(3))
