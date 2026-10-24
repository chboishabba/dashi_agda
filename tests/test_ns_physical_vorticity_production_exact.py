"""Exact physical Galerkin triad to vorticity-stretching calibration.

Original PDE identity: classical Fourier/curl identity for unforced,
periodic Navier--Stokes; not attributable to R236 or Shahmurov as an
original discovery. R236/R685/R690 are DASHI source owners, which are
not proved equivalent to this physical functional by this test.
Coefficients use the normalized torus Fourier convention.
"""
import sympy as S

I=S.I
P=(1,0,0); Q=(0,1,2); K=(1,1,2)

def vector(mode):
    return S.Matrix(mode)

def cdot(a,b):
    return S.simplify((S.conjugate(a).T*b)[0])

def seed(sign=1):
    field={P:S.Matrix([0,1,1]),Q:S.Matrix([1,0,0]),
           K:sign*I*S.Matrix([1,-1,0])}
    field.update({tuple(-x for x in m):S.conjugate(v)
                  for m,v in list(field.items())})
    return field

def leray(mode, v):
    n=vector(mode)
    return S.simplify(v-n*n.dot(v)/n.dot(n))

def exact_budget(field):
    for mode, coeff in field.items():
        assert S.simplify(vector(mode).dot(coeff))==0
        assert field[tuple(-x for x in mode)]==S.conjugate(coeff)
    omega={m:I*vector(m).cross(u) for m,u in field.items()}
    energy=ens=stretch=S.Integer(0)
    for m,um in field.items():
        conv=S.zeros(3,1)
        vortex_stretch=S.zeros(3,1)
        for p,up in field.items():
            q=tuple(m[j]-p[j] for j in range(3))
            if q in field:
                conv+=vector(q).dot(up)*field[q]
                vortex_stretch+=I*vector(q).dot(omega[p])*field[q]
        nonlin=-I*leray(m,conv)
        energy+=2*S.re(cdot(um,nonlin))
        ens+=2*S.re(cdot(um,nonlin))*vector(m).dot(vector(m))
        stretch+=2*S.re(cdot(omega[m],vortex_stretch))
    return tuple(S.simplify(z) for z in (energy,ens,stretch))

def test_nontrivial_physical_stretching_positive_and_negative():
    assert exact_budget(seed())==(0,8,8)
    assert exact_budget(seed(-1))==(0,-8,-8)

def test_zero_coefficients_do_not_alter_any_physical_budget():
    original=seed()
    padded=original.copy()
    for m in ((10,0,0),(-10,0,0),(0,10,0),(0,-10,0)):
        padded[m]=S.zeros(3,1)
    assert exact_budget(padded)==exact_budget(original)

def test_amplitude_scaling_shows_no_dissipation_only_uniform_payment():
    field=seed()
    energy=sum(S.simplify(cdot(v,v)) for v in field.values())
    enstrophy=sum(sum(x*x for x in m)*cdot(v,v) for m,v in field.items())
    palinstrophy=sum(sum(x*x for x in m)**2*cdot(v,v)
                     for m,v in field.items())
    assert (energy,enstrophy,palinstrophy)==(10,38,198)
    for amp in (S.Integer(1),S.Integer(2),S.Integer(50)):
        scaled={m:amp*v for m,v in field.items()}
        assert exact_budget(scaled)==(0,8*amp**3,8*amp**3)
    # At viscosity 1, d/dt ||omega||_2^2 = 8 a^3 - 396 a^2.
    assert 8*50**3-2*198*50**2==10_000
    # This is an *instantaneous* smooth trigonometric datum, not blowup.

def test_real_part_only_map_loses_helical_phase_and_stretching():
    physical=seed()
    real_only={m:v.applyfunc(S.re) for m,v in physical.items()}
    assert exact_budget(physical)==(0,8,8)
    assert exact_budget(real_only)==(0,0,0)
    # Real vector coordinates in the existing Round42 input carrier
    # are not automatically the real physical Fourier field: imaginary
    # Fourier phases must be preserved by paired real/imag components.
