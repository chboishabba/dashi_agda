from collections import deque
import itertools
import numpy as np

P = 3
B = np.array([
    [2,2,0,0,0],
    [2,2,2,0,2],
    [0,2,2,2,0],
    [0,0,2,2,0],
    [0,2,0,0,2],
], dtype=int) % P
E = np.array([
    [1,1,1],
    [0,0,2],
    [0,1,2],
    [2,0,2],
    [0,0,1],
], dtype=int) % P
R = np.array([1,0,2], dtype=int)
SIMPLE_ROOTS = (
    (1,0,0,0,0),
    (0,1,0,0,0),
    (0,0,1,0,0),
    (0,0,0,1,0),
    (0,0,0,0,1),
    (0,0,2,1,1),
)


def key(a):
    return tuple(int(x) for x in np.array(a).reshape(-1))


def rank_mod3(a):
    a = np.array(a, dtype=int) % 3
    r = 0
    for c in range(a.shape[1]):
        pivot = next((i for i in range(r, a.shape[0]) if a[i,c]), None)
        if pivot is None:
            continue
        a[[r,pivot]] = a[[pivot,r]]
        if a[r,c] == 2:
            a[r] = 2*a[r] % 3
        for i in range(a.shape[0]):
            if i != r and a[i,c]:
                a[i] = (a[i] - a[i,c]*a[r]) % 3
        r += 1
    return r


def inv_mod3(a):
    a = np.array(a, dtype=int) % 3
    n = a.shape[0]
    aug = np.concatenate([a, np.eye(n, dtype=int)], axis=1)
    r = 0
    for c in range(n):
        pivot = next(i for i in range(r, n) if aug[i,c])
        aug[[r,pivot]] = aug[[pivot,r]]
        if aug[r,c] == 2:
            aug[r] = 2*aug[r] % 3
        for i in range(n):
            if i != r and aug[i,c]:
                aug[i] = (aug[i] - aug[i,c]*aug[r]) % 3
        r += 1
    return aug[:,n:] % 3


def left_inverse(e):
    for rows in itertools.combinations(range(5),3):
        m = e[list(rows),:]
        if rank_mod3(m) == 3:
            left = np.zeros((3,5), dtype=int)
            left[:,list(rows)] = inv_mod3(m)
            assert np.array_equal(left @ e % 3, np.eye(3, dtype=int))
            return left
    raise AssertionError


def reflection(root):
    r = np.array(root, dtype=int).reshape(5,1)
    return (np.eye(5, dtype=int) - r @ (r.T @ B)) % 3


def matrix_group(gens):
    ident = np.eye(5, dtype=int)
    seen = {key(ident): ident}
    queue = deque([ident])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = s @ g % 3
            k = key(h)
            if k not in seen:
                seen[k] = h
                queue.append(h)
    return list(seen.values())


def normalize_ell(ell):
    ell = np.array(ell, dtype=int) % 3
    value = int(ell @ R) % 3
    assert value != 0
    return ell * (1 if value == 1 else 2) % 3


def ell_from_pair(pair):
    b,c = pair
    return np.array([(1+c)%3, b, c], dtype=int)


def pair_from_ell(ell):
    ell = normalize_ell(ell)
    assert int(ell[0]) == (1 + int(ell[2])) % 3
    return int(ell[1]), int(ell[2])


def det2(a):
    return (int(a[0,0])*int(a[1,1]) - int(a[0,1])*int(a[1,0])) % 3


def verify():
    left = left_inverse(E)
    weyl = matrix_group([reflection(r) for r in SIMPLE_ROOTS])
    assert len(weyl) == 51840

    local = {}
    h3_stabilizer_order = 0
    for g in weyl:
        t = left @ g @ E % 3
        if np.array_equal(E @ t % 3, g @ E % 3):
            h3_stabilizer_order += 1
            local[key(t)] = t
    assert h3_stabilizer_order == 432
    assert len(local) == 72

    pairs = list(itertools.product(range(3), repeat=2))
    affine = []
    for t in local.values():
        tinv = inv_mod3(t)
        mapping = {p: pair_from_ell(ell_from_pair(p) @ tinv % 3) for p in pairs}
        shift = np.array(mapping[(0,0)], dtype=int)
        col1 = (np.array(mapping[(1,0)], dtype=int) - shift) % 3
        col2 = (np.array(mapping[(0,1)], dtype=int) - shift) % 3
        a = np.stack([col1,col2], axis=1) % 3
        assert all(tuple((a @ np.array(p,dtype=int) + shift) % 3) == mapping[p] for p in pairs)
        affine.append((a,shift))

    linear_parts = {key(a):a for a,b in affine}
    translations = {tuple(int(x) for x in b) for a,b in affine}
    assert len(linear_parts) == 8
    assert len(translations) == 9
    identity2 = np.eye(2, dtype=int)
    assert all(np.array_equal(a.T @ a % 3, identity2) for a in linear_parts.values())

    # Exhaustively recover O(2,3) inside GL(2,3).
    gl2 = []
    for vals in itertools.product(range(3), repeat=4):
        a = np.array(vals,dtype=int).reshape(2,2)
        if det2(a) != 0:
            gl2.append(a)
    orthogonal = {key(a):a for a in gl2 if np.array_equal(a.T @ a % 3, identity2)}
    assert len(orthogonal) == 8
    assert set(linear_parts) == set(orthogonal)

    norm1 = [v for v in pairs if v != (0,0) and (v[0]*v[0] + v[1]*v[1]) % 3 == 1]
    norm2 = [v for v in pairs if (v[0]*v[0] + v[1]*v[1]) % 3 == 2]
    assert set(norm1) == {(1,0),(2,0),(0,1),(0,2)}
    assert set(norm2) == {(1,1),(1,2),(2,1),(2,2)}

    return {
        "h3_stabilizer_order": h3_stabilizer_order,
        "order_parameter_action_order": len(affine),
        "translation_subgroup_size": len(translations),
        "orthogonal_linear_part_size": len(linear_parts),
        "action_is_F3_squared_semidirect_O2_3": True,
        "norm1_neighbor_count": len(norm1),
        "norm2_shell_count": len(norm2),
        "norm1_is_axial_C3xC3_adjacency": True,
        "canonical_quadratic_displacement_invariant": True,
        "physical_kinetic_coefficient_derived": False,
    }


if __name__ == "__main__":
    for k,v in verify().items():
        print(f"{k}: {v}")
