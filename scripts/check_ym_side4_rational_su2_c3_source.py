#!/usr/bin/env python3
"""Independent finite exact-arithmetic reference for the YM side-four C3/Wilson
source max-cut. Not an Agda kernel proof, not a Haar/continuum result.

Uses literal four-axis site and spatial action, and norm-one rational
quaternion link group. Exhaustively checks 256*4 source positive bond
commutations, closed positive length-four Wilson paths, and gauge invariance.
Historical Wilson/Balaban and existing DASHI proof owners retain credit.
"""
from fractions import Fraction as F
from itertools import product

N = 4
AXES = range(4)
SITES = list(product(range(N), repeat=4))
O = (F(1), F(0), F(0), F(0))
I = (F(0), F(1), F(0), F(0))
J = (F(0), F(0), F(1), F(0))
K = (F(0), F(0), F(0), F(1))
R = (F(3, 5), F(4, 5), F(0), F(0))
Q = (O, I, J, K, R, tuple(-v for v in O), tuple(-v for v in I))


def product_q(a, b):
    w, x, y, z = a
    s, p, q, r = b
    return (w*s-x*p-y*q-z*r,
            w*p+x*s+y*r-z*q,
            w*q-x*r+y*s+z*p,
            w*r+x*q-y*p+z*s)


def inv(a):
    w, x, y, z = a
    return w, -x, -y, -z


def next_site(site, axis):
    r = list(site)
    r[axis] = (r[axis] + 1) % N
    return tuple(r)


def c3_site(s):
    return s[0], s[3], s[1], s[2]


def c3_axis(axis):
    return (0, 2, 3, 1)[axis]


def source_field(site, axis):
    # Deterministic, nontrivial rational SU2 assignment.
    h = 11*site[0] + 7*site[1] + 5*site[2] + 3*site[3] + axis
    return Q[h % len(Q)]


def source_gauge(site):
    return Q[(site[0] + 2*site[1] + 3*site[2] + site[3]) % len(Q)]


def c3_field(site, axis):
    return source_field(c3_site(site), c3_axis(axis))


def gauge_field(site, axis):
    return product_q(product_q(source_gauge(site), c3_field(site, axis)),
                     inv(source_gauge(next_site(site, axis))))


def holonomy(site, directions, field):
    result = O
    here = site
    for axis in directions:
        result = product_q(result, field(here, axis))
        here = next_site(here, axis)
    return here, result


def run():
    count_bonds = 0
    count_positive_paths = 0
    count_gauge_wilson = 0
    for s in SITES:
        assert c3_site(c3_site(c3_site(s))) == s
        for a in AXES:
            assert c3_axis(c3_axis(c3_axis(a))) == a
            assert next_site(c3_site(s), c3_axis(a)) == c3_site(next_site(s, a))
            count_bonds += 1

            # Transported non-closed positive word: no hidden negative
            # orientation or fake loop projection.
            word = (a, (a + 1) % 4, (a + 2) % 4)
            c3_word = tuple(c3_axis(b) for b in word)
            old_final, old_h = holonomy(c3_site(s), c3_word, source_field)
            new_final, new_h = holonomy(s, word, c3_field)
            assert old_final == c3_site(new_final) and old_h == new_h
            count_positive_paths += 1

            # Four turns in the same periodic direction close exactly.
            loop = (a, a, a, a)
            dest, h = holonomy(s, loop, c3_field)
            assert dest == s
            transformed_dest, ht = holonomy(c3_site(s), tuple(c3_axis(b) for b in loop), source_field)
            assert transformed_dest == c3_site(s)
            assert h == ht
            gd, gh = holonomy(s, loop, gauge_field)
            assert gd == s
            assert gh == product_q(product_q(source_gauge(s), h), inv(source_gauge(s)))
            assert gh[0] == h[0] == ht[0]
            count_gauge_wilson += 1

    count_trace = 0
    for h, x in product(Q, repeat=2):
        assert sum(v*v for v in h) == sum(v*v for v in x) == 1
        assert product_q(h, x)[0] == product_q(x, h)[0]
        assert product_q(product_q(h, x), inv(h))[0] == x[0]
        count_trace += 1

    return {
        "side4_sites": len(SITES),
        "positive_bonds_tested": count_bonds,
        "open_c3_path_tests": count_positive_paths,
        "closed_gauge_c3_wilson_tests": count_gauge_wilson,
        "rational_trace_conjugation_tests": count_trace,
        "result": "PASS (finite exact rational arithmetic; Agda kernel not executed)",
    }


if __name__ == "__main__":
    import json
    print(json.dumps(run(), indent=2, sort_keys=True))


# Extended same-source check for *all* signed orientations and the 16 ordered
# coordinate pairs at every one of the 256 sites. This is the finite ordered
# action, NOT the convention-specific physical six-plaquette Wilson action.
def signed_holonomy(site, word, field):
    product_value = O
    for axis, sign in word:
        if sign:
            product_value = product_q(product_value, field(site, axis))
            site = next_site(site, axis)
        else:
            prev = list(site)
            prev[axis] = (prev[axis] - 1) % N
            site = tuple(prev)
            product_value = product_q(product_value, inv(field(site, axis)))
    return site, product_value


def ordered_action_check():
    original_action = F(0)
    c3_action = F(0)
    checked = 0
    for site in SITES:
        for a in AXES:
            for b in AXES:
                word = ((a, True), (b, True), (a, False), (b, False))
                end, orig = signed_holonomy(site, word, source_field)
                c3_end, c3_value = signed_holonomy(site, word, c3_field)
                moved_end, moved_value = signed_holonomy(
                    c3_site(site),
                    tuple((c3_axis(axis), orientation)
                          for axis, orientation in word),
                    source_field,
                )
                assert end == site
                assert c3_end == site and moved_end == c3_site(site)
                assert c3_value == moved_value
                original_action += orig[0]
                c3_action += c3_value[0]
                checked += 1
    assert original_action == c3_action
    return {
        "all_ordered_plaq_tests": checked,
        "sum_before_C3": str(original_action),
        "sum_after_C3": str(c3_action),
        "result": "PASS (exact Fraction; not physical six-plane/Haar)",
    }


if __name__ == "__main__":
    print(json.dumps(ordered_action_check(), indent=2, sort_keys=True))
