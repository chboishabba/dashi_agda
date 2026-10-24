"""B finite physical curl compensation under swap-closed R236 regions.

Provenance: classical curl identity, Bony paraproduct geometry; DASHI's
strict R63 and selected R236 carrier definitions. This confirms the
physical enstrophy carrier, NOT an equality to the different-degree
R236 mixed-helicity coherent covariance or R685/R690 functional.
"""
import importlib.util
from pathlib import Path
import sympy as S

P=Path(__file__).resolve().parents[1]/"scripts/ns_physical_vorticity_partition.py"
spec=importlib.util.spec_from_file_location("physical_ns_partition",P)
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)

def test_swap_residual_is_universal_polynomial_identity():
    assert mod.symbolic_swapped_curl_defect_certificate()

def test_critical_and_deep_selector_invariant_under_ordered_swap():
    triples=[
       ((1,0,0),(0,1,8)),
       ((1,0,0),(0,1,64)),
       ((2,1,0),(0,3,32)),
       ((4,0,0),(-4,1,0)),
       ((1,5,0),(-1,-5,1))
    ]
    for p,q in triples:
        assert mod.r236(p,q).replace("LH","L").replace("HL","L") == (
               mod.r236(q,p).replace("LH","L").replace("HL","L"))

def test_critical_and_deep_curl_defect_cancel_separately():
    p=(1,0,0)
    field=mod.field(p,(0,1,64))
    for q in ((0,1,8),(0,3,32)):
        for k,v in mod.field(p,q).items():
            field[k]=field.get(k,S.zeros(3,1))+v
    proof=mod.budget(field)
    assert proof["production"]==proof["stretch"]
    assert sum(v[1] for v in proof["region_correction"].values())==0
    assert all(v[3]==0 for v in proof["region_correction"].values())
    assert sum(v[0] for v in proof["region_correction"].values())==proof["production"]
    assert sum(v[2] for v in proof["region_correction"].values())==proof["stretch"]

def test_selected_physical_critical_identity_retains_transport_exactly():
    p=(1,0,0)
    field=mod.field(p,(0,1,64))
    for k,v in mod.field(p,(0,1,8)).items():
        field[k]=field.get(k,S.zeros(3,1))+v
    proof=mod.budget(field)
    crit=proof["region_correction"].get("critical",(0,0,0,0))
    deep=[v for k,v in proof["region_correction"].items() if k!="critical"]
    assert crit[0]==crit[1]+crit[2]
    assert crit[3]==0
    assert S.simplify(crit[1]+sum(v[1] for v in deep))==0

def test_quartic_covariance_cannot_equal_cubic_physical_stretching_for_all_amplitudes():
    # R236 live coherent covariance is n*W(M,D)+(sum r)*W(M,M),
    # where modal M and D are bilinear in the physical velocity,
    # hence degree FOUR. Physical nonlinear enstrophy is degree THREE.
    a=S.symbols("a",positive=True)
    A1,A2,r1,r2=S.Integer(1),S.Integer(2),S.Integer(1),S.Integer(2)
    M=A1+A2;decay=-(r1*A1+r2*A2)
    cov=2*M*decay+(r1+r2)*M*M
    assert cov==-3
    assert S.expand(2*(a*a*M)*(a*a*decay)
                    +(r1+r2)*(a*a*M)**2-a**4*cov)==0
    # Nonzero physical stretching from the already verified six-mode datum:
    # P(a u)=8 a^3. No source-identical equality for all a.
    assert S.simplify((a**4*cov-8*a**3).subs(a,1))==-11
    assert S.simplify((a**4*cov-8*a**3).subs(a,2))==-112
