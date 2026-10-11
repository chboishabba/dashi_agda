from __future__ import annotations

from itertools import combinations, product
import numpy as np

from scripts.exceptional_f4_derivation_maxcut_probe import (
    inner_derivation_matrices,
    independent_indices_mod3,
    rank_mod3,
)

P = 3


def inv_mod3(a):
    a = np.asarray(a, dtype=np.int8).copy() % P
    n = a.shape[0]
    aug = np.concatenate([a, np.eye(n, dtype=np.int8)], axis=1) % P
    r = 0
    for c in range(n):
        piv = np.flatnonzero(aug[r:, c])
        if piv.size == 0:
            raise ValueError("singular")
        p = r + int(piv[0])
        if p != r:
            aug[[r, p]] = aug[[p, r]]
        if aug[r, c] == 2:
            aug[r] = 2 * aug[r] % P
        for rr in range(n):
            if rr != r and aug[rr, c]:
                aug[rr] = (aug[rr] - aug[rr, c] * aug[r]) % P
        r += 1
    return aug[:, n:] % P


def joint_weight_dimensions(operators, dimension):
    out = {}
    eye = np.eye(dimension, dtype=np.int8)
    for weight in product(range(3), repeat=len(operators)):
        stacked = np.vstack([
            (op - weight[i] * eye) % P
            for i, op in enumerate(operators)
        ])
        d = dimension - rank_mod3(stacked)
        if d:
            out[weight] = d
    return out


def standard_f4_mod3_roots():
    roots = set()
    for i in range(4):
        for s in (1, 2):
            v = [0] * 4
            v[i] = s
            roots.add(tuple(v))
    for i in range(4):
        for j in range(i + 1, 4):
            for si in (1, 2):
                for sj in (1, 2):
                    v = [0] * 4
                    v[i] = si
                    v[j] = sj
                    roots.add(tuple(v))
    for signs in product((1, 2), repeat=4):
        roots.add(tuple(signs))
    assert len(roots) == 48
    return roots


def verify():
    inner = [d.astype(np.int8) % P for d in inner_derivation_matrices()]
    flat = np.asarray([d.reshape(-1) for d in inner], dtype=np.int8)
    chosen = independent_indices_mod3(flat)
    derivation_basis = [inner[i] for i in chosen]
    basis_flat = flat[chosen]
    assert len(derivation_basis) == 52

    toral_indices = [
        i for i, d in enumerate(inner)
        if np.array_equal(d @ d @ d % P, d)
    ]
    assert len(toral_indices) == 12
    toral = [inner[i] for i in toral_indices]

    selected = None
    for choice in combinations(range(len(toral)), 4):
        hs = [toral[i] for i in choice]
        if rank_mod3(np.asarray([h.reshape(-1) for h in hs])) != 4:
            continue
        if all(
            not np.any((a @ b - b @ a) % P)
            for a, b in combinations(hs, 2)
        ):
            selected = choice
            break
    assert selected is not None
    H = [toral[i] for i in selected]

    carrier_weights = joint_weight_dimensions(H, 27)
    assert carrier_weights[(0, 0, 0, 0)] == 3
    assert len(carrier_weights) == 25
    assert sorted(d for w, d in carrier_weights.items() if w != (0, 0, 0, 0)) == [1] * 24

    pivot_columns = independent_indices_mod3(basis_flat.T)
    square = basis_flat[:, pivot_columns]
    square_inverse = inv_mod3(square)

    ad_h = []
    for h in H:
        action = np.zeros((52, 52), dtype=np.int8)
        for j, d in enumerate(derivation_basis):
            bracket = ((h @ d - d @ h) % P).reshape(-1)
            action[:, j] = bracket[pivot_columns] @ square_inverse % P
        assert np.array_equal(action @ action @ action % P, action)
        ad_h.append(action)

    adjoint_weights = joint_weight_dimensions(ad_h, 52)
    assert adjoint_weights[(0, 0, 0, 0)] == 4
    roots = {w for w, d in adjoint_weights.items() if w != (0, 0, 0, 0)}
    assert len(roots) == 48
    assert all(adjoint_weights[w] == 1 for w in roots)

    # Explicit same-root-set recognition found by projective incidence search.
    change = np.array([
        [1, 2, 1, 1],
        [1, 1, 2, 1],
        [2, 2, 2, 2],
        [0, 0, 0, 1],
    ], dtype=np.int8)
    assert rank_mod3(change) == 4
    transported = {
        tuple((np.asarray(root, dtype=np.int8) @ change % P).tolist())
        for root in roots
    }
    standard = standard_f4_mod3_roots()
    assert transported == standard

    return {
        "primitive_toral_derivations": len(toral_indices),
        "selected_torus_indices": selected,
        "carrier_zero_weight_dimension": carrier_weights[(0, 0, 0, 0)],
        "carrier_nonzero_weight_count": len(carrier_weights) - 1,
        "adjoint_zero_weight_dimension": adjoint_weights[(0, 0, 0, 0)],
        "adjoint_root_count": len(roots),
        "root_spaces_one_dimensional": all(adjoint_weights[w] == 1 for w in roots),
        "gl4_change": change.tolist(),
        "transported_root_set_equals_standard_f4_mod3": transported == standard,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
