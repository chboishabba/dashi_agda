#!/usr/bin/env python3
from __future__ import annotations
import itertools, json
from collections import Counter
from dataclasses import dataclass

SELECTED_MODULI = {
    4: (1, 0, 1, 1, 1),       # x^4 + x^3 + x^2 + 1
    5: (1, 0, 0, 0, 2, 1),    # x^5 + 2x^4 + 1
    6: (1, 0, 0, 0, 1, 1, 1), # x^6 + x^5 + x^4 + 1
}


def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] % 3 == 0:
        p.pop()
    return tuple(x % 3 for x in p)


def _poly_divmod(a, b):
    a = list(_trim(a)); b = list(_trim(b))
    if b == [0]:
        raise ZeroDivisionError
    q = [0] * max(1, len(a) - len(b) + 1)
    inv = 1 if b[-1] % 3 == 1 else 2
    while len(a) >= len(b) and any(a):
        k = len(a) - len(b)
        c = a[-1] * inv % 3
        q[k] = c
        for i, bi in enumerate(b):
            a[i + k] = (a[i + k] - c * bi) % 3
        a = list(_trim(a))
    return tuple(q), tuple(a)


def is_irreducible(modulus):
    modulus = _trim(modulus)
    n = len(modulus) - 1
    if n < 1 or modulus[-1] != 1:
        return False
    for d in range(1, n // 2 + 1):
        for coeffs in itertools.product(range(3), repeat=d):
            divisor = tuple(coeffs) + (1,)
            if _poly_divmod(modulus, divisor)[1] == (0,):
                return False
    return True


@dataclass(frozen=True)
class GF3Extension:
    degree: int
    modulus: tuple[int, ...]

    def __post_init__(self):
        if len(self.modulus) != self.degree + 1 or self.modulus[-1] != 1:
            raise ValueError('modulus must be monic of selected degree')
        if not is_irreducible(self.modulus):
            raise ValueError('modulus is reducible')

    @property
    def order(self): return 3 ** self.degree
    @property
    def zero(self): return (0,) * self.degree
    @property
    def one(self): return (1,) + (0,) * (self.degree - 1)
    @property
    def elements(self): return list(itertools.product(range(3), repeat=self.degree))

    def from_int(self, n):
        out = []
        for _ in range(self.degree):
            out.append(n % 3); n //= 3
        return tuple(out)

    def add(self, a, b): return tuple((x + y) % 3 for x, y in zip(a, b))
    def neg(self, a): return tuple((-x) % 3 for x in a)

    def mul(self, a, b):
        d = self.degree
        c = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i + j] = (c[i + j] + x * y) % 3
        lower = self.modulus[:-1]
        for k in range(2 * d - 2, d - 1, -1):
            coef = c[k] % 3
            if coef:
                for j, mj in enumerate(lower):
                    c[k - d + j] = (c[k - d + j] - coef * mj) % 3
                c[k] = 0
        return tuple(c[:d])

    def pow(self, a, n):
        r = self.one
        while n:
            if n & 1:
                r = self.mul(r, a)
            a = self.mul(a, a); n //= 2
        return r

    def inv(self, a):
        if a == self.zero:
            raise ZeroDivisionError
        return self.pow(a, self.order - 2)

    def frobenius(self, a): return self.pow(a, 3)


def model_for_degree(d):
    return GF3Extension(d, SELECTED_MODULI[d])


def orbit_profile(states, action):
    states = list(states); seen = set(); out = Counter()
    for s in states:
        if s in seen:
            continue
        orbit = []; x = s
        while x not in orbit:
            orbit.append(x); seen.add(x); x = action(x)
        out[len(orbit)] += 1
    return dict(sorted(out.items()))


def multiplicative_order(model, a):
    if a == model.zero:
        return 0
    x = model.one
    for k in range(1, model.order):
        x = model.mul(x, a)
        if x == model.one:
            return k
    raise AssertionError('nonzero field element failed finite order')


def find_primitive_element(model):
    target = model.order - 1
    for a in model.elements:
        if a != model.zero and multiplicative_order(model, a) == target:
            return a
    raise AssertionError('no primitive element found')


def legacy_first_enabled_step(s):
    a, b, c, d = s
    if a > 0: return a - 1, b, c + 1, d
    if c > 0: return a, b, c - 1, d + 1
    if d > 0: return a + 1, b, c, d - 1
    if b > 0: return a + 1, b - 1, c, d
    return s


def legacy_states_exact_mass(total):
    out = []
    for a in range(total + 1):
        for b in range(total - a + 1):
            for c in range(total - a - b + 1):
                out.append((a, b, c, total - a - b - c))
    return out


def row_major_displacement_count(states, step, cols):
    ix = {s: i for i, s in enumerate(states)}
    vectors = set()
    for s in states:
        i, j = ix[s], ix[step(s)]
        r, c = divmod(i, cols); rr, cc = divmod(j, cols)
        vectors.add((rr - r, cc - c))
    return len(vectors)


def scan_row_major_displacements(total_mass=18, min_cols=2, max_cols=200):
    states = legacy_states_exact_mass(total_mass)
    counts = {cols: row_major_displacement_count(states, legacy_first_enabled_step, cols)
              for cols in range(min_cols, max_cols + 1)}
    minimum = min(counts.values())
    return {
        'node_count': len(states),
        'minimum_vector_count': minimum,
        'minimum_vector_columns': [c for c, n in counts.items() if n == minimum],
        'matching_12_vector_columns': [c for c, n in counts.items() if n == 12],
        'column_scan': counts,
    }


def full_signed_weave_frontier():
    return {
        'lane_count': 15,
        'pointed_lane_to_full_valuation_paid': True,
        'signed_multiplicity_and_program_machinery_paid': True,
        'canonical_total_step_over_full_signed_state_found': False,
        'full_signed_transition_graph_claimed': False,
        'reason': ('SignedSSPFRACTRANWeaveExact owns the 15-lane valuation/program carriers '
                   'but no canonical total transition over SignedSSPExecutionState; inventing '
                   'one would exceed the formal source.'),
    }


def recognition_summary():
    fields = {}
    for d in (4, 5, 6):
        m = model_for_degree(d)
        nonzero = [x for x in m.elements if x != m.zero]
        primitive = find_primitive_element(m)
        fields[str(d)] = {
            'order': m.order,
            'modulus_low_to_high': list(m.modulus),
            'frobenius_orbits': orbit_profile(m.elements, m.frobenius),
            'negation_orbits_all': orbit_profile(m.elements, m.neg),
            'negation_orbits_nonzero': orbit_profile(nonzero, m.neg),
            'primitive_element': list(primitive),
            'primitive_order': multiplicative_order(m, primitive),
            'kernel_coordinate_object_map_paid': True,
            'c2_negation_action_intertwining_paid': True,
            'chosen_field_multiplication_runtime_verified': True,
            'canonical_field_multiplication_from_existing_repo_action': False,
            'full_recognition_paid': False,
        }
    return {
        'fields': fields,
        'row_major_12_vector_scan': scan_row_major_displacements(),
        'full_signed_weave_frontier': full_signed_weave_frontier(),
    }


def main():
    print(json.dumps(recognition_summary(), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
