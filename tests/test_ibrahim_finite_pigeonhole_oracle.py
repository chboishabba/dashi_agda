"""Independent finite-pigeonhole mathematical regression for Agda collision producer.

Original first-link methodology: Ibrahim, Danforth, Dodds 2017,
DOI 10.1016/j.jocs.2016.12.001. Tests new DASHI theorem interpretation,
not an Agda compiler or Wikipedia corpus execution receipt.
"""
from __future__ import annotations
import random
import unittest


def finite_orbit_collision(nodes, next_edge, start):
    """N+1 orbit observations; first repeated encoded node gives i<j."""
    if not set(nodes).issuperset(next_edge):
        raise ValueError('enumeration does not cover all source vertices')
    if not nodes or any(next_edge[v] not in next_edge for v in next_edge):
        raise ValueError('only nonempty total functional graphs')
    # Duplicated entries are allowed; encode selects any covering occurrence.
    index = {v: nodes.index(v) for v in next_edge}
    orbit = []
    x = start
    for _ in range(len(nodes) + 1):
        orbit.append(x)
        x = next_edge[x]
    for j in range(1, len(orbit)):
        for i in range(j):
            if index[orbit[i]] == index[orbit[j]]:
                return i, j - i, orbit
    raise AssertionError('finite pigeonhole contradicted')


class FinitePigeonholeOracleTests(unittest.TestCase):
    def test_all_one_and_two_vertex_functional_graphs(self):
        for n in (1, 2):
            import itertools
            keys = [f'v{i}' for i in range(n)]
            for targets in itertools.product(keys, repeat=n):
                graph = dict(zip(keys, targets))
                for start in keys:
                    entry, period, orbit = finite_orbit_collision(keys, graph, start)
                    self.assertGreater(period, 0)
                    self.assertLess(entry + period, len(orbit))
                    self.assertEqual(orbit[entry], orbit[entry + period])

    def test_random_complete_graphs_nonminimal_enumerations(self):
        rng = random.Random(20261114)
        for n in range(1, 15):
            keys = [f'v{i}' for i in range(n)]
            for _ in range(400):
                graph = {key: rng.choice(keys) for key in keys}
                carrier = keys + [rng.choice(keys) for __ in range(rng.randrange(4))]
                rng.shuffle(carrier)
                for start in rng.sample(keys, min(3, n)):
                    entry, period, orbit = finite_orbit_collision(carrier, graph, start)
                    self.assertLess(entry + period, len(carrier) + 1)
                    self.assertEqual(orbit[entry], orbit[entry + period])
                    self.assertTrue(period >= 1)
                    self.assertEqual(entry + (period - 1) + 1, entry + period)

    def test_partial_and_missing_source_rejected(self):
        with self.assertRaises(ValueError):
            finite_orbit_collision(['a'], {'a': 'missing'}, 'a')
        with self.assertRaises(ValueError):
            finite_orbit_collision([], {'a': 'a'}, 'a')


if __name__ == '__main__':
    unittest.main()
