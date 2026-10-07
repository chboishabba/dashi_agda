#!/usr/bin/env python3
from __future__ import annotations
import argparse, itertools, json
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

SELECTED_MODULI = {
    4: (1, 0, 1, 1, 1),
    5: (1, 0, 0, 0, 2, 1),
    6: (1, 0, 0, 0, 1, 1, 1),
}


def _trim(p):
    p = list(p)
    while len(p) > 1 and p[-1] % 3 == 0: p.pop()
    return tuple(x % 3 for x in p)


def _poly_divmod(a, b):
    a = list(_trim(a)); b = list(_trim(b))
    if b == [0]: raise ZeroDivisionError
    q = [0] * max(1, len(a) - len(b) + 1)
    inv = 1 if b[-1] % 3 == 1 else 2
    while len(a) >= len(b) and any(a):
        k = len(a) - len(b); c = a[-1] * inv % 3; q[k] = c
        for i, bi in enumerate(b): a[i + k] = (a[i + k] - c * bi) % 3
        a = list(_trim(a))
    return tuple(q), tuple(a)


def is_irreducible(modulus):
    modulus = _trim(modulus); n = len(modulus) - 1
    if n < 1 or modulus[-1] != 1: return False
    for d in range(1, n // 2 + 1):
        for coeffs in itertools.product(range(3), repeat=d):
            if _poly_divmod(modulus, tuple(coeffs) + (1,))[1] == (0,): return False
    return True


@dataclass(frozen=True)
class GF3Extension:
    degree: int
    modulus: tuple[int, ...]
    def __post_init__(self):
        if len(self.modulus) != self.degree + 1 or self.modulus[-1] != 1: raise ValueError('bad modulus')
        if not is_irreducible(self.modulus): raise ValueError('reducible modulus')
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
        for _ in range(self.degree): out.append(n % 3); n //= 3
        return tuple(out)
    def add(self, a, b): return tuple((x + y) % 3 for x, y in zip(a, b))
    def neg(self, a): return tuple((-x) % 3 for x in a)
    def mul(self, a, b):
        d = self.degree; c = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): c[i + j] = (c[i + j] + x * y) % 3
        lower = self.modulus[:-1]
        for k in range(2 * d - 2, d - 1, -1):
            coef = c[k] % 3
            if coef:
                for j, mj in enumerate(lower): c[k - d + j] = (c[k - d + j] - coef * mj) % 3
                c[k] = 0
        return tuple(c[:d])
    def pow(self, a, n):
        r = self.one
        while n:
            if n & 1: r = self.mul(r, a)
            a = self.mul(a, a); n //= 2
        return r
    def inv(self, a):
        if a == self.zero: raise ZeroDivisionError
        return self.pow(a, self.order - 2)
    def frobenius(self, a): return self.pow(a, 3)


def model_for_degree(d): return GF3Extension(d, SELECTED_MODULI[d])


def orbit_profile(states, action):
    seen = set(); out = Counter()
    for s in states:
        if s in seen: continue
        orbit = []; x = s
        while x not in orbit: orbit.append(x); seen.add(x); x = action(x)
        out[len(orbit)] += 1
    return dict(sorted(out.items()))


def multiplicative_order(model, a):
    if a == model.zero: return 0
    x = model.one
    for k in range(1, model.order):
        x = model.mul(x, a)
        if x == model.one: return k
    raise AssertionError('finite order missing')


def find_primitive_element(model):
    for a in model.elements:
        if a != model.zero and multiplicative_order(model, a) == model.order - 1: return a
    raise AssertionError('primitive element missing')


def k4_gf9_linear_image():
    return [(a, b, (-b) % 3, 0) for a in range(3) for b in range(3)]


def heisenberg_translate(axis, x):
    y = list(x); y[axis] = (y[axis] + 1) % 3; return tuple(y)


def kernel_add(a, b): return tuple((x + y) % 3 for x, y in zip(a, b))


def heisenberg_additive_intertwiner_verified():
    for x in itertools.product(range(3), repeat=6):
        for axis in range(6):
            basis = tuple(1 if i == axis else 0 for i in range(6))
            if heisenberg_translate(axis, x) != kernel_add(basis, x): return False
    for x4 in itertools.product(range(3), repeat=4):
        x6 = x4 + (0, 0)
        for axis in range(4):
            basis4 = tuple(1 if i == axis else 0 for i in range(4))
            if heisenberg_translate(axis, x6) != kernel_add(basis4, x4) + (0, 0): return False
    return True


def legacy_first_enabled_step(s):
    a, b, c, d = s
    if a > 0: return a - 1, b, c + 1, d
    if c > 0: return a, b, c - 1, d + 1
    if d > 0: return a + 1, b, c, d - 1
    if b > 0: return a + 1, b - 1, c, d
    return s


def legacy_states_exact_mass(total):
    return [(a, b, c, total-a-b-c)
            for a in range(total + 1)
            for b in range(total - a + 1)
            for c in range(total - a - b + 1)]


def row_major_displacement_count(states, step, cols):
    ix = {s: i for i, s in enumerate(states)}; vectors = set()
    for s in states:
        i, j = ix[s], ix[step(s)]; r, c = divmod(i, cols); rr, cc = divmod(j, cols)
        vectors.add((rr-r, cc-c))
    return len(vectors)


def scan_row_major_displacements(total_mass=18, min_cols=2, max_cols=200):
    states = legacy_states_exact_mass(total_mass)
    counts = {c: row_major_displacement_count(states, legacy_first_enabled_step, c)
              for c in range(min_cols, max_cols + 1)}
    minimum = min(counts.values())
    return {'node_count': len(states), 'minimum_vector_count': minimum,
            'minimum_vector_columns': [c for c, n in counts.items() if n == minimum],
            'matching_12_vector_columns': [c for c, n in counts.items() if n == 12]}


def full_signed_weave_frontier():
    return {
        'lane_count': 15,
        'pointed_lane_to_full_valuation_paid': True,
        'signed_multiplicity_and_program_machinery_paid': True,
        'canonical_total_program_counter_machine_paid': True,
        'machine_to_rich_signed_state_projection_paid': False,
        'canonical_total_step_over_summary_state_alone_found': False,
        'full_rich_signed_transition_graph_claimed': False,
        'reason': ('The remaining program list makes the scheduler total. WeaveEffect retains counts rather than prime identity, '
                   'while SignedSSPExecutionState additionally owns address/residual/length metadata; a faithful projection '
                   'therefore still needs an independent witness.')
    }


def recognition_summary():
    fields = {}
    for d in (4, 5, 6):
        m = model_for_degree(d); nonzero = [x for x in m.elements if x != m.zero]; primitive = find_primitive_element(m)
        fields[str(d)] = {'order': m.order, 'modulus_low_to_high': list(m.modulus),
            'frobenius_orbits': orbit_profile(m.elements, m.frobenius),
            'negation_orbits_all': orbit_profile(m.elements, m.neg),
            'negation_orbits_nonzero': orbit_profile(nonzero, m.neg),
            'primitive_element': list(primitive), 'primitive_order': multiplicative_order(m, primitive),
            'kernel_coordinate_object_map_paid': True, 'c2_negation_action_intertwining_paid': True,
            'chosen_field_multiplication_runtime_verified': True,
            'canonical_field_multiplication_from_existing_repo_action': False, 'full_recognition_paid': False}
    m4 = model_for_degree(4); gf9 = set(k4_gf9_linear_image())
    fields['4']['gf9_subfield_linear_image_size'] = len(gf9)
    fields['4']['gf9_subfield_equals_frobenius2_fixed_set'] = gf9 == {x for x in m4.elements if m4.pow(x, 9) == x}
    fields['4']['gf9_subfield_is_naive_prefix_k2'] = gf9 == {(a,b,0,0) for a in range(3) for b in range(3)}
    fields['4']['t5_chosen_subfield_lattice_object_map_paid'] = True
    return {
        'fields': fields,
        'existing_heisenberg_translation_intertwines_f3_addition': heisenberg_additive_intertwiner_verified(),
        'row_major_12_vector_scan': scan_row_major_displacements(),
        'full_signed_weave_frontier': full_signed_weave_frontier()
    }


def main():
    p = argparse.ArgumentParser(); p.add_argument('--output', type=Path); args = p.parse_args()
    text = json.dumps(recognition_summary(), indent=2, sort_keys=True) + '\n'
    if args.output: args.output.parent.mkdir(parents=True, exist_ok=True); args.output.write_text(text)
    else: print(text, end='')

if __name__ == '__main__': main()
