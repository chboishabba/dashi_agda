import sympy as sp

I = sp.I


def hermitian_su3_basis():
    out = []
    for i in range(3):
        for j in range(i+1,3):
            s = sp.zeros(3); s[i,j] = 1; s[j,i] = 1
            a = sp.zeros(3); a[i,j] = -I; a[j,i] = I
            out.append((f"S{i+1}{j+1}", s))
            out.append((f"A{i+1}{j+1}", a))
    out.append(("T3", sp.diag(1,-1,0)))
    out.append(("X", sp.diag(1,1,-2)))
    return out


BASIS = hermitian_su3_basis()


def stabilizer_matrix(vevs):
    xl = sp.symbols('l0:8', real=True)
    xr = sp.symbols('r0:8', real=True)
    hl = sum((xl[k]*BASIS[k][1] for k in range(8)), sp.zeros(3))
    hr = sum((xr[k]*BASIS[k][1] for k in range(8)), sp.zeros(3))
    equations = []
    for z in vevs:
        delta = hl*z - z*hr
        for entry in list(delta):
            re, im = sp.expand_complex(entry).as_real_imag()
            equations.extend((re,im))
    matrix, rhs = sp.linear_eq_to_matrix(equations, xl+xr)
    assert all(x == 0 for x in rhs)
    return matrix, xl, xr


def verify():
    e32 = sp.zeros(3); e32[2,1] = 1
    e33 = sp.zeros(3); e33[2,2] = 1

    one, _, _ = stabilizer_matrix([e33])
    two, _, _ = stabilizer_matrix([e32,e33])
    one_dim = 16 - one.rank()
    two_dim = 16 - two.rank()
    assert one_dim == 7
    assert two_dim == 4

    null = two.nullspace()
    assert len(null) == 4

    # First three kernel directions are the standard SU(2)_L generators
    # S12, A12, T3_L. The fourth is X_L + 3 T3_R + X_R.
    expected = []
    v = sp.zeros(16,1); v[0] = 1; expected.append(v)
    v = sp.zeros(16,1); v[1] = 1; expected.append(v)
    v = sp.zeros(16,1); v[6] = 1; expected.append(v)
    v = sp.zeros(16,1); v[7] = 1; v[8+6] = 3; v[8+7] = 1; expected.append(v)
    assert all(two*v == sp.zeros(two.rows,1) for v in expected)
    assert sp.Matrix.hstack(*expected).rank() == 4

    # Same hypercharge generator used by the existing trinification bridge.
    xL = sp.diag(1,1,-2)
    xR = sp.diag(1,1,-2)
    t3R = sp.diag(1,-1,0)
    yL = -sp.Rational(1,6)*xL
    yR = -sp.Rational(1,6)*xR - sp.Rational(1,2)*t3R
    assert yL*e32 - e32*yR == sp.zeros(3)
    assert yL*e33 - e33*yR == sp.zeros(3)

    # Full SU(3)^3 has dimension 24; color is untouched, while the L/R
    # stabilizer has dimension 4. Thus 12 L/R generators are broken and the
    # compact low-energy Lie algebra has dimension 8+4=12.
    broken_lr = two.rank()
    assert broken_lr == 12

    return {
        "one_neutral_vev_lr_stabilizer_dimension": one_dim,
        "two_independent_neutral_vevs_lr_stabilizer_dimension": two_dim,
        "surviving_lr_generators": "su2_L + u1_Y",
        "surviving_u1_generator": "-(X_L + 3*T3_R + X_R)/6",
        "both_vevs_hypercharge_neutral": True,
        "color_su3_untouched": True,
        "full_low_energy_lie_algebra_dimension": 12,
        "broken_lr_generator_count": broken_lr,
        "conditional_gauge_mass_matrix_rank": broken_lr,
        "physical_vev_scale_derived": False,
        "higgs_potential_selects_these_vevs": False,
    }


if __name__ == "__main__":
    for k,v in verify().items():
        print(f"{k}: {v}")
