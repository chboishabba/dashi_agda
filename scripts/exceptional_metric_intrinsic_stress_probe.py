from fractions import Fraction as F


def mat_add(a, b):
    return [[a[i][j] + b[i][j] for j in range(4)] for i in range(4)]


def mat_scale(s, a):
    return [[s * a[i][j] for j in range(4)] for i in range(4)]


def mat_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]


def verify():
    # Set alpha=1; the general result scales linearly at the stationary origin.
    eta = [
        [F(-1), 0, 0, 0],
        [0, F(1), 0, 0],
        [0, 0, F(1), 0],
        [0, 0, 0, F(1)],
    ]
    G = mat_scale(F(1, 27), [
        [12, 0, 0, 0],
        [0, -8, 0, 1],
        [0, 0, -8, 0],
        [0, 1, 0, -8],
    ])
    radiation = mat_scale(F(1, 27), [
        [3, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 0, 1, 0],
        [0, 1, 0, 1],
    ])
    vacuum = mat_scale(F(-1, 3), eta)
    assert mat_add(radiation, vacuum) == G

    # Two counter-propagating radiation pairs: I_y=1/27 and I_plus=2/27.
    pair_y = mat_scale(F(1, 27), [
        [1, 0, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 0],
    ])
    pair_plus = mat_scale(F(1, 27), [
        [2, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 0, 0, 0],
        [0, 1, 0, 1],
    ])
    assert mat_add(pair_y, pair_plus) == radiation

    # Trace and dominant-energy shape.
    assert -radiation[0][0] + radiation[1][1] + radiation[2][2] + radiation[3][3] == 0
    energy = radiation[0][0]
    principal_pressures = (F(0), F(1, 27), F(2, 27))
    assert all(abs(p) <= energy for p in principal_pressures)
    assert sum(principal_pressures, F(0)) == energy

    # Rainich single-Maxwell necessary algebraic condition fails:
    # T^mu_nu squared must be proportional to identity for a non-null EM field.
    mixed = mat_mul(eta, radiation)
    mixed_square = mat_mul(mixed, mixed)
    diag = [mixed_square[i][i] for i in range(4)]
    offdiag_nonzero = any(mixed_square[i][j] != 0 for i in range(4) for j in range(4) if i != j)
    rainich_proportional_identity = (not offdiag_nonzero) and len(set(diag)) == 1
    assert not rainich_proportional_identity

    return {
        "einstein_origin_alpha1": G,
        "vacuum_coefficient": F(1, 3),
        "radiation_origin_alpha1": radiation,
        "radiation_pair_intensities": (F(1, 27), F(2, 27)),
        "radiation_trace_zero": True,
        "dominant_energy_shape": True,
        "principal_pressures": principal_pressures,
        "single_maxwell_rainich_condition": False,
        "multi_mode_or_multi_internal_component_required": True,
        "exact_decomposition": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
