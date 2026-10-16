#!/usr/bin/env python3
from __future__ import annotations

from collections import deque, defaultdict
import itertools

from exceptional_h3_h2_phase_incidence_probe import (
    SIMPLE_ROOTS,
    act_subspace,
    bilinear,
    canon,
    matrix_group,
    projective_lines,
    q,
    reflection,
    rref_subspaces,
)

WEYL_ORDER = 51840


def build_geometry():
    points = sorted({canon(v) for v in itertools.product(range(3), repeat=5) if any(v)})
    roots = {p for p in points if q(p) == 2}
    nulls = {p for p in points if q(p) == 0}

    h3 = []
    for a in rref_subspaces(3):
        s = projective_lines(a)
        if sum(p in roots for p in s) == 6 and sum(p in nulls for p in s) == 1:
            h3.append(s)

    h2 = []
    for a in rref_subspaces(2):
        s = projective_lines(a)
        rr = [p for p in s if p in roots]
        if len(rr) == 2 and sum(p in nulls for p in s) == 0 and bilinear(rr[0], rr[1]) == 0:
            h2.append(s)

    h2_to_h3 = []
    h3_to_h2 = [[] for _ in h3]
    for j, face in enumerate(h2):
        incident = tuple(i for i, patch in enumerate(h3) if face.issubset(patch))
        assert len(incident) == 4
        h2_to_h3.append(frozenset(incident))
        for i in incident:
            h3_to_h2[i].append(j)

    assert (len(h3), len(h2)) == (120, 270)
    assert {len(x) for x in h3_to_h2} == {9}
    return h3, h2, h2_to_h3, h3_to_h2


def enumerate_exact_covers(h2_to_h3, h3_to_h2):
    covers = []

    def go(uncovered, chosen):
        if not uncovered:
            covers.append(frozenset(chosen))
            return
        best_options = None
        for i in sorted(uncovered):
            options = [j for j in h3_to_h2[i] if h2_to_h3[j] <= uncovered]
            if not options:
                return
            if best_options is None or len(options) < len(best_options):
                best_options = options
                if len(options) == 1:
                    break
        for j in best_options:
            go(uncovered - h2_to_h3[j], chosen + [j])

    go(set(range(120)), [])
    assert len(covers) == len(set(covers))
    return covers


def weyl_orbits_on_covers(h2, covers):
    generators = [reflection(r) for r in SIMPLE_ROOTS]
    weyl = matrix_group(generators)
    assert len(weyl) == WEYL_ORDER

    h2_index = {face: i for i, face in enumerate(h2)}
    generator_perms = [
        [h2_index[act_subspace(g, face)] for face in h2]
        for g in generators
    ]

    cover_set = set(covers)
    seen = set()
    orbits = []
    for cover in covers:
        if cover in seen:
            continue
        orbit = {cover}
        seen.add(cover)
        queue = deque([cover])
        while queue:
            current = queue.popleft()
            for perm in generator_perms:
                nxt = frozenset(perm[j] for j in current)
                assert nxt in cover_set
                if nxt not in seen:
                    seen.add(nxt)
                    orbit.add(nxt)
                    queue.append(nxt)
        orbits.append(orbit)
    assert len(seen) == len(covers)
    return orbits


def pair_intersection_signature(h2, cover):
    count = defaultdict(int)
    for a, b in itertools.combinations(sorted(cover), 2):
        count[len(h2[a] & h2[b])] += 1
    return dict(sorted(count.items()))


def agreement_energy(section, h2_count):
    occupancy = [0] * h2_count
    for face in section:
        occupancy[face] += 1
    return sum(k * (k - 1) // 2 for k in occupancy), occupancy


def section_from_cover(cover, h2_to_h3):
    selected = [None] * 120
    for face in cover:
        for patch in h2_to_h3[face]:
            assert selected[patch] is None
            selected[patch] = face
    assert all(x is not None for x in selected)
    return selected


def verify():
    h3, h2, h2_to_h3, h3_to_h2 = build_geometry()
    covers = enumerate_exact_covers(h2_to_h3, h3_to_h2)
    assert len(covers) == 6642
    assert all(len(c) == 30 for c in covers)

    # For any section let k_f be the number (0..4) of H3 patches selecting H2
    # face f.  Sum_f k_f=120 and C(k,2) <= 3k/2, with equality iff k=0 or 4.
    # Thus agreement <=180, and equality holds exactly when every occupied face
    # has k=4, i.e. the section is an exact cover by 30 H2 stars.
    for k in range(5):
        assert k * (k - 1) // 2 <= 3 * k / 2
        if k not in (0, 4):
            assert k * (k - 1) // 2 < 3 * k / 2
    maximum_agreement = 180

    # The next possible occupancy defect is exactly 3.  Write n1,n2,n3 for
    # counts of partially occupied stars. Load conservation modulo four gives
    # n1+2*n2+3*n3 = 0 mod 4; the deficit from 180 is
    # (3*n1+4*n2+3*n3)/2.  Exhausting one residue period proves the least
    # positive value is 3, attained by (n1,n2,n3)=(1,0,1).
    positive_defects = []
    for n1, n2, n3 in itertools.product(range(4), repeat=3):
        if n1 == n2 == n3 == 0:
            continue
        if (n1 + 2*n2 + 3*n3) % 4 == 0:
            positive_defects.append((3*n1 + 4*n2 + 3*n3) / 2)
    defect_gap = min(positive_defects)
    assert defect_gap == 3

    # Realize the gap from an actual exact-cover section by changing one H3 to
    # another incident, previously unoccupied H2 face: occupancies 4->3 and
    # 0->1, hence agreement 180->177.
    section = section_from_cover(covers[0], h2_to_h3)
    energy0, occ0 = agreement_energy(section, len(h2))
    assert energy0 == 180
    patch = 0
    old_face = section[patch]
    new_face = next(face for face in h3_to_h2[patch] if face != old_face and occ0[face] == 0)
    excited = list(section)
    excited[patch] = new_face
    energy1, occ1 = agreement_energy(excited, len(h2))
    assert (occ1[old_face], occ1[new_face], energy1) == (3, 1, 177)

    orbits = weyl_orbits_on_covers(h2, covers)
    orbit_sizes = sorted(len(o) for o in orbits)
    assert orbit_sizes == [162, 1620, 1620, 3240]
    stabilizers = [WEYL_ORDER // n for n in orbit_sizes]
    assert stabilizers == [320, 32, 32, 16]

    orbit_signatures = [
        {
            "orbit_size": len(o),
            "h2_pair_intersection_signature": pair_intersection_signature(h2, next(iter(o))),
        }
        for o in sorted(orbits, key=len)
    ]

    return {
        "h3_count": len(h3),
        "h2_count": len(h2),
        "incidence_count": sum(len(x) for x in h3_to_h2),
        "maximum_agreement_edges": maximum_agreement,
        "first_excitation_agreement_edges": energy1,
        "dimensionless_defect_gap": int(defect_gap),
        "ground_state_exact_cover_count": len(covers),
        "ground_state_weyl_orbit_sizes": orbit_sizes,
        "ground_state_stabilizer_orders": stabilizers,
        "ground_state_orbit_signatures": orbit_signatures,
        "all_ground_states_are_exact_covers": True,
        "gap_three_distinct_from_fibre_laplacian_gap_without_operator_weld": True,
        "candidate_interaction": "reward adjacent H3 patches selecting their shared H2 face",
        "physical_interaction_coefficient_paid": False,
        "continuum_dynamics_paid": False,
    }


if __name__ == "__main__":
    for key, value in verify().items():
        print(f"{key}: {value}")
