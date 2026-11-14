"""Physical A Duhamel source-response transfer, NOT regularity continuation."""
import importlib.util
from pathlib import Path
import sympy as S

P=Path(__file__).resolve().parents[1]/"scripts/ns_a_physical_duhamel_maximal_l2.py"
spec=importlib.util.spec_from_file_location("ns_a_physical_duhamel",P)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def test_positive_kernel_Jensen_Tonelli_mass():
    a,t,T,x=S.symbols("a t T x",positive=True)
    assert S.simplify(S.integrate(a*S.exp(-a*t),(t,0,T))-
                      (1-S.exp(-a*T)))==0
    assert S.simplify(S.integrate(a*S.exp(-a*(t-x)),(t,x,T))-
                      (1-S.exp(-a*(T-x))))==0

def test_exact_nonautonomous_Duhamel_scalar():
    receipt=mod.exact_exponential_certificate()
    assert receipt["source_norm_squared"]=="1/4"
    assert receipt["duhamel_norm_squared"]=="1/12"
    assert receipt["L2_contraction"]
    assert "critical A2" in receipt["not_claimed"]
    assert "global A3" in receipt["not_claimed"]

def test_signed_discrete_causal_kernel_contracts_without_cardinality_tax():
    assert mod.exact_discrete_causal_check()
