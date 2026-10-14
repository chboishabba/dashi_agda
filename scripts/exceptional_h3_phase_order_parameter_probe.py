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
SIMPLE_ROOTS = (
    (1,0,0,0,0),
    (0,1,0,0,0),
    (0,0,1,0,0),
    (0,0,0,1,0),
    (0,0,0,0,1),
    (0,0,2,1,1),
)
E = np.array([
    [1,1,1],
    [0,0,2],
    [0,1,2],
    [2,0,2],
    [0,0,1],
], dtype=int) % P
ELL = np.array([1,0,2], dtype=int) % P
RADICAL = np.array([1,0,2], dtype=int) % P


def key(a):
    return tuple(int(x) for x in np.array(a).reshape(-1))


def reflection(root):
    r = np.array(root, dtype=int).reshape(5,1)
    return (np.eye(5, dtype=int) - r @ (r.T @ B)) % P


def matrix_group(gens):
    ident = np.eye(5, dtype=int)
    seen = {key(ident): ident}
    queue = deque([ident])
    while queue:
        g = queue.popleft()
        for s in gens:
            h = s @ g % P
            k = key(h)
            if k not in seen:
                seen[k] = h
                queue.append(h)
    return list(seen.values())


def inv_mod3(a):
    a = np.array(a, dtype=int) % 3
    n = a.shape[0]
    aug = np.concatenate([a, np.eye(n, dtype=int)], axis=1)
    r = 0
    for c in range(n):
        pivot = next(i for i in range(r, n) if aug[i,c])
        aug[[r,pivot]] = aug[[pivot,r]]
        if aug[r,c] == 2:
            aug[r] = 2 * aug[r] % 3
        for i in range(n):
            if i != r and aug[i,c]:
                aug[i] = (aug[i] - aug[i,c] * aug[r]) % 3
        r += 1
    return aug[:,n:] % 3


def left_inverse(e):
    for rows in itertools.combinations(range(e.shape[0]), e.shape[1]):
        a = e[list(rows), :]
        if int(round(np.linalg.det(a))) % 3:
            left = np.zeros((e.shape[1], e.shape[0]), dtype=int)
            left[:, list(rows)] = inv_mod3(a)
            assert np.array_equal(left @ e % 3, np.eye(e.shape[1], dtype=int))
            return left
    raise AssertionError("no independent row minor")


def canon_covector(v):
    v = tuple(int(x) % 3 for x in v)
    for x in v:
        if x:
            s = 1 if x == 1 else 2
            return tuple(s*y % 3 for y in v)
    raise ValueError("zero covector")


def verify():
    weyl = matrix_group([reflection(r) for r in SIMPLE_ROOTS])
    assert len(weyl) == 51840
    left = left_inverse(E)

    stabilizer = []
    local_image = {}
    for g in weyl:
        t = left @ g @ E % 3
        if np.array_equal(E @ t % 3, g @ E % 3):
            stabilizer.append(g)
            local_image[key(t)] = t
    assert len(stabilizer) == 432
    assert len(local_image) == 72

    projective_orbit = {
        canon_covector(ELL @ t % 3)
        for t in local_image.values()
    }
    resolving_lines = {
        canon_covector(v)
        for v in itertools.product(range(3), repeat=3)
        if any(v) and (np.array(v, dtype=int) @ RADICAL) % 3 != 0
    }
    assert projective_orbit == resolving_lines
    assert len(projective_orbit) == 9

    local_line_stabilizer = [
        t for t in local_image.values()
        if canon_covector(ELL @ t % 3) == canon_covector(ELL)
    ]
    upstairs_line_stabilizer = []
    for g in stabilizer:
        t = left @ g @ E % 3
        if canon_covector(ELL @ t % 3) == canon_covector(ELL):
            upstairs_line_stabilizer.append(g)
    assert len(local_line_stabilizer) == 8
    assert len(upstairs_line_stabilizer) == 48
    assert len(stabilizer) // len(upstairs_line_stabilizer) == 9

    return {
        "weyl_order": len(weyl),
        "selected_h3_stabilizer_order": len(stabilizer),
        "selected_h3_local_image_order": len(local_image),
        "radical_resolving_projective_covectors": len(resolving_lines),
        "phase_line_orbit_size": len(projective_orbit),
        "phase_line_stabilizer_order": len(upstairs_line_stabilizer),
        "local_phase_line_stabilizer_order": len(local_line_stabilizer),
        "phase_orbit_is_all_radical_resolving_lines": True,
        "bare_h3_geometry_selects_unique_phase_line": False,
        "phase_line_is_symmetry_breaking_order_parameter": True,
    }


if __name__ == "__main__":
    for k, v in verify().items():
        print(f"{k}: {v}")
