import numpy as np

P = 3
G_PLUS = np.array([[1,0,1],[0,1,0],[1,0,1]], dtype=int) % P
G_MINUS = np.array([[1,0,2],[0,1,0],[2,0,1]], dtype=int) % P
T = np.array([[2,0,1],[0,1,0],[1,0,0]], dtype=int) % P
ELL_PLUS = np.array([1,0,2], dtype=int) % P
ELL_MINUS = np.array([2,0,0], dtype=int) % P


def inv_mod3(a):
    a = np.array(a, dtype=int) % 3
    n = a.shape[0]
    aug = np.concatenate([a, np.eye(n, dtype=int)], axis=1)
    r = 0
    for c in range(n):
        pivot = next(i for i in range(r, n) if aug[i, c] % 3)
        aug[[r, pivot]] = aug[[pivot, r]]
        if aug[r, c] == 2:
            aug[r] = 2 * aug[r] % 3
        for i in range(n):
            if i != r and aug[i, c]:
                aug[i] = (aug[i] - aug[i, c] * aug[r]) % 3
        r += 1
    return aug[:, n:] % 3


def det3(m):
    m = np.array(m, dtype=int)
    return int(round(np.linalg.det(m))) % 3


def verify():
    tinv = inv_mod3(T)
    assert np.array_equal(ELL_PLUS @ tinv % 3, ELL_MINUS)
    assert np.array_equal(ELL_MINUS @ T % 3, ELL_PLUS)

    L_PLUS = (G_PLUS + np.outer(ELL_PLUS, ELL_PLUS)) % 3
    L_MINUS = (G_MINUS + np.outer(ELL_MINUS, ELL_MINUS)) % 3

    assert det3(G_PLUS) == 0
    assert det3(G_MINUS) == 0
    assert det3(L_PLUS) != 0
    assert det3(L_MINUS) != 0
    assert np.array_equal(T.T @ L_MINUS @ T % 3, L_PLUS)

    # The three-point fibre automorphism group is Aff(1,F3)=S3.
    # Translations change only the phase origin; the differential multiplier is a in {1,2}.
    # Since a^2=1 mod 3, ell^T ell is invariant under the full affine fibre symmetry.
    affine_cases = []
    for a in (1, 2):
        for b in (0, 1, 2):
            images = tuple((a*x + b) % 3 for x in range(3))
            assert len(set(images)) == 3
            assert (a*a) % 3 == 1
            affine_cases.append((a, b, images))

    return {
        "phase_covector_plus": ELL_PLUS.tolist(),
        "phase_covector_minus": ELL_MINUS.tolist(),
        "plus_lifted_gram": L_PLUS.tolist(),
        "minus_lifted_gram": L_MINUS.tolist(),
        "plus_lifted_det_mod3": det3(L_PLUS),
        "minus_lifted_det_mod3": det3(L_MINUS),
        "weyl_covariant_lift": True,
        "affine_fibre_automorphisms_checked": len(affine_cases),
        "orientation_inversion_leaves_metric_term_invariant": True,
        "global_h3_phase_bundle_identified_with_e8_zeta": False,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
