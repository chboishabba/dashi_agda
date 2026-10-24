"""Exact Schwartz Fourier convolution/Leray calibration of the whole-space A carrier."""
import importlib.util
from pathlib import Path
import sympy as S

SCRIPT=Path(__file__).resolve().parents[1]/"scripts/ns_a_schwartz_fourier_same_object.py"
SPEC=importlib.util.spec_from_file_location("ns_a_schwartz",SCRIPT)
module=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(module)

def test_exact_real_spatial_and_fourier_same_object():
    data=module.certificate()
    assert data["divergence"]=="0"
    assert data["fourier_convection_direct"]==data["fourier_convection_convolution"]
    assert data["finite_energy"]
    assert len(data["leray_projected"])==3

def test_physical_schwartz_energy_and_nonlinear_leray_are_nontrivial():
    x,y,z,a,b,c=S.symbols("x y z xi_x xi_y xi_z",real=True)
    r2=x*x+y*y+z*z
    psi=S.exp(-r2)
    u=S.Matrix([S.diff(psi,y),-S.diff(psi,x),0])
    expected=-4*S.Matrix([x,y,0])*S.exp(-2*r2)
    computed=S.Matrix([S.simplify(sum(u[j]*S.diff(u[i],(x,y,z)[j])
                   for j in range(3))) for i in range(3)])
    assert all(S.simplify(computed[i]-expected[i])==0 for i in range(3))
    norm2=a*a+b*b+c*c
    F=S.I*(S.pi/2)**S.Rational(3,2)*S.exp(-norm2/8)
    projected=F*S.Matrix([
        a*c*c/norm2,b*c*c/norm2,-c*(a*a+b*b)/norm2
    ])
    assert S.simplify(S.Matrix([a,b,c]).dot(projected))==0
    assert S.simplify(projected[0].subs({a:1,b:0,c:1}))!=0

def test_no_global_regulariy_or_unjustified_transform_claim():
    data=module.certificate()
    not_claimed=" ".join(data["source_only_not_claimed"])
    assert "every solution" in not_claimed
    assert "time propagation" in not_claimed
    assert "kernel certification" in not_claimed
