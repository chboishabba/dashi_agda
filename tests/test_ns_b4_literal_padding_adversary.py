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
    assert module.region((6,0,0),(-5,1,0))=="noncore"

def test_literal_b4_padding_exact_certificates():
    results={n:module.certificate(n) for n in (4,5,8,12,16,20)}
    assert results[4]["signed_defect"]=="0"
    for n in (5,8,12,16,20):
        assert results[n]["core_rows"]==882
        assert results[n]["literal_core_companion"]=="10123708"
    assert results[5]["signed_defect"]=="18080"
    assert results[8]["signed_defect"]=="535344"
    assert results[12]["signed_defect"]=="4204080"
    assert results[16]["signed_defect"]=="17577776"
    assert results[20]["signed_defect"]=="53228080"
    assert results[16]["defect_exceeds_half_companion"]
    assert results[20]["defect_exceeds_half_companion"]

def test_no_renormalization_by_ignoring_zero_cells():
    n8=module.certificate(8)
    n16=module.certificate(16)
    assert n8["noncore_zero_amplitude_rows"]==3470
    assert n16["noncore_zero_amplitude_rows"]==32910
    assert Fraction(n16["signed_defect"])>Fraction(n8["signed_defect"])
    assert n16["literal_core_companion"]==n8["literal_core_companion"]

def test_unbounded_positive_subfamily_of_zero_amplitude_rows():
    # For each integer m>=6, p=(m,0,0), q=(1-m,1,0) is a noncore
    # row when cutoff N>=m. Its rate excess is exactly 2*m*(m-1).
    for m in (6,7,10,20,50):
        p=(m,0,0)
        q=(1-m,1,0)
        assert module.region(p,q)=="noncore"
        assert sum(x*x for x in p+q)-2==2*m*(m-1)
    assert sum(2*m*(m-1) for m in range(6,17)) <= int(
        module.certificate(16)["signed_defect"])
