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


def canon(v):
    v = tuple(int(x) % 3 for x in v)
    for a in v:
        if a:
            s = 1 if a == 1 else 2
            return tuple(s*x % 3 for x in v)
    raise ValueError("zero")


def bilinear(u, v):
    return int(np.array(u) @ B @ np.array(v)) % 3


def q(v):
    return bilinear(v, v)


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


def inv3(a):
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
    for rows in itertools.combinations(range(5), 3):
        m = e[list(rows), :]
        if rank_mod3(m) == 3:
            left = np.zeros((3,5), dtype=int)
            left[:,list(rows)] = inv3(m)
            assert np.array_equal(left @ e % 3, np.eye(3, dtype=int))
            return left
    raise AssertionError("no left inverse")


def rref_subspaces(dim):
    for pivots in itertools.combinations(range(5), dim):
        base = np.zeros((dim,5), dtype=int)
        for i,p in enumerate(pivots):
            base[i,p] = 1
        nonp = [j for j in range(5) if j not in pivots]
        free = [(i,j) for i,p in enumerate(pivots) for j in nonp if j > p]
        for vals in itertools.product(range(3), repeat=len(free)):
            a = base.copy()
            for (i,j),v in zip(free, vals):
                a[i,j] = v
            yield a


def projective_lines(a):
    out = set()
    dim = a.shape[0]
    for coeffs in itertools.product(range(3), repeat=dim):
        if not any(coeffs):
            continue
        v = sum((coeffs[i]*a[i] for i in range(dim)), np.zeros(5, dtype=int)) % 3
        out.add(canon(v))
    return frozenset(out)


def choose_basis_cols(lines):
    cols = []
    for p in sorted(lines):
        candidate = cols + [np.array(p, dtype=int)]
        if rank_mod3(np.stack(candidate, axis=1)) > len(cols):
            cols.append(np.array(p, dtype=int))
            if len(cols) == 3:
                break
    return np.stack(cols, axis=1) % 3


def plane_from_two(p, r):
    out = set()
    for a,b in itertools.product(range(3), repeat=2):
        if a == b == 0:
            continue
        out.add(canon(tuple((a*p[i] + b*r[i]) % 3 for i in range(5))))
    return frozenset(out)


def annihilator_line(coord_lines):
    found = set()
    for ell in itertools.product(range(3), repeat=3):
        if not any(ell):
            continue
        if all(sum(ell[i]*v[i] for i in range(3)) % 3 == 0 for v in coord_lines):
            found.add(canon(ell))
    assert len(found) == 1
    return np.array(next(iter(found)), dtype=int)


def reflection(root):
    r = np.array(root, dtype=int).reshape(5,1)
    return (np.eye(5, dtype=int) - r @ (r.T @ B)) % 3


def key(a):
    return tuple(int(x) for x in np.array(a).reshape(-1))


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


def act_line(g, p):
    return canon(g @ np.array(p, dtype=int) % 3)


def act_subspace(g, s):
    return frozenset(act_line(g, p) for p in s)


def verify():
    points = sorted({canon(v) for v in itertools.product(range(3), repeat=5) if any(v)})
    roots = {p for p in points if q(p) == 2}
    nulls = {p for p in points if q(p) == 0}
    assert (len(roots), len(nulls)) == (36,40)

    h3 = []
    for a in rref_subspaces(3):
        s = projective_lines(a)
        if sum(p in roots for p in s) == 6 and sum(p in nulls for p in s) == 1:
            h3.append(s)
    assert len(h3) == 120

    h2 = []
    for a in rref_subspaces(2):
        s = projective_lines(a)
        rr = [p for p in s if p in roots]
        if len(rr) == 2 and sum(p in nulls for p in s) == 0 and bilinear(rr[0], rr[1]) == 0:
            h2.append(s)
    assert len(h2) == 270

    incidences = [(i,j) for i,h in enumerate(h3) for j,p in enumerate(h2) if p.issubset(h)]
    assert len(incidences) == 1080
    assert {sum(i == k for i,j in incidences) for k in range(120)} == {9}
    assert {sum(j == k for i,j in incidences) for k in range(270)} == {4}

    # For every H3, the nine incident H2s are exactly the nine 2-planes
    # complementary to the unique null/radical line.
    for i,h in enumerate(h3):
        radical = next(p for p in h if p in nulls)
        all_planes = set()
        for p,r in itertools.combinations(sorted(h), 2):
            plane = plane_from_two(p,r)
            if len(plane) == 4 and plane.issubset(h):
                all_planes.add(plane)
        complements = {p for p in all_planes if radical not in p}
        incident = {h2[j] for ii,j in incidences if ii == i}
        assert len(all_planes) == 13
        assert len(complements) == 9
        assert complements == incident

    # Build the decorated metric on every H3-H2 flag and verify nondegeneracy.
    h3_index = {h:i for i,h in enumerate(h3)}
    h2_index = {h:i for i,h in enumerate(h2)}
    bases = []
    decorated = {}
    determinants = set()
    for i,h in enumerate(h3):
        e = choose_basis_cols(h)
        left = left_inverse(e)
        gram = e.T @ B @ e % 3
        assert rank_mod3(gram) == 2
        bases.append((e,left,gram))
        for ii,j in incidences:
            if ii != i:
                continue
            coord_lines = [tuple(left @ np.array(p,dtype=int) % 3) for p in h2[j]]
            ell = annihilator_line(coord_lines)
            radical = next(p for p in h if p in nulls)
            rcoord = left @ np.array(radical,dtype=int) % 3
            assert int(ell @ rcoord) % 3 != 0
            metric = (gram + np.outer(ell,ell)) % 3
            assert rank_mod3(metric) == 3
            determinants.add(int(round(np.linalg.det(metric))) % 3)
            decorated[(i,j)] = (ell,metric)
    assert determinants == {1}
    assert len(decorated) == 1080

    # Weyl covariance for all flags under all six simple reflections.
    generators = [reflection(r) for r in SIMPLE_ROOTS]
    transition_checks = 0
    for (i,j),(ell,metric) in decorated.items():
        e,left,gram = bases[i]
        for g in generators:
            hp = act_subspace(g,h3[i])
            pp = act_subspace(g,h2[j])
            ip = h3_index[hp]
            jp = h2_index[pp]
            ep,leftp,gramp = bases[ip]
            t = leftp @ g @ e % 3
            assert np.array_equal(g @ e % 3, ep @ t % 3)
            metricp = decorated[(ip,jp)][1]
            assert np.array_equal(t.T @ metricp @ t % 3, metric)
            transition_checks += 1
    assert transition_checks == 6480

    # Independent orbit-stabilizer check on one flag.
    weyl = matrix_group(generators)
    assert len(weyl) == 51840
    h = h3[0]
    p = next(h2[j] for i,j in incidences if i == 0)
    h_stab = [g for g in weyl if act_subspace(g,h) == h]
    flag_stab = [g for g in h_stab if act_subspace(g,p) == p]
    assert (len(h_stab), len(flag_stab)) == (432,48)

    return {
        "h3_count": len(h3),
        "h2_count": len(h2),
        "h3_h2_incidence_count": len(incidences),
        "h2_per_h3": 9,
        "h3_per_h2": 4,
        "kernel_complements_equal_incident_h2_for_all_h3": True,
        "decorated_metric_count": len(decorated),
        "decorated_metric_determinant_mod3": 1,
        "simple_reflection_transition_checks": transition_checks,
        "weyl_covariant_decorated_metric": True,
        "selected_h3_stabilizer_order": len(h_stab),
        "selected_h3_h2_flag_stabilizer_order": len(flag_stab),
        "phase_line_equals_incident_h2_face_same_object": True,
    }


if __name__ == "__main__":
    for k,v in verify().items():
        print(f"{k}: {v}")
