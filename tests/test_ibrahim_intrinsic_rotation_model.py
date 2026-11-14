"""Model check for the Agda intrinsic cycle claim; not a kernel or Wikipedia receipt."""
from __future__ import annotations
import random
import unittest


def orbit(graph, start, count):
    out = [start]
    for _ in range(count):
        out.append(graph[out[-1]])
    return out


def earliest_cycle(path):
    seen = {}
    for i, node in enumerate(path):
        if node in seen:
            return seen[node], i - seen[node]
        seen[node] = i
    raise ValueError("too few steps to observe a cycle")


def reachable_within_period(graph, start, target, period):
    current = start
    for _ in range(period):
        if current == target:
            return True
        current = graph[current]
    return False


class IntrinsicRotationModelTests(unittest.TestCase):
    def test_9000_random_same_start_certificates_canonical_root(self):
        rng = random.Random(20261115)
        checked = 0
        for size in range(1, 31):
            for _ in range(300):
                graph = [rng.randrange(size) for _ in range(size)]
                source = rng.randrange(size)
                path = orbit(graph, source, 6 * size + 10)
                entry, period = earliest_cycle(path)
                self.assertGreater(period, 0)
                first = entry + rng.randrange(0, 3 * size + 1)
                second = entry + rng.randrange(0, 3 * size + 1)
                a, b = path[first], path[second]
                self.assertEqual(path[first + period], a)
                self.assertEqual(path[second + period], b)
                self.assertTrue(reachable_within_period(graph, a, b, period))
                self.assertTrue(reachable_within_period(graph, b, a, period))
                self.assertEqual(min(path[first:first + period]),
                                 min(path[second:second + period]))
                checked += 1
        self.assertEqual(checked, 9000)

    def test_independent_terminal_cycles_not_equivalent(self):
        graph = [1, 0, 3, 2]
        self.assertFalse(reachable_within_period(graph, 0, 2, 2))
        self.assertFalse(reachable_within_period(graph, 2, 0, 2))

    def test_transient_prefix_is_not_a_cycle(self):
        graph = [1, 2, 3, 2]
        self.assertEqual(earliest_cycle(orbit(graph, 0, 10)), (2, 2))
        self.assertFalse(reachable_within_period(graph, 2, 0, 2))

    def test_dead_end_is_not_an_unknown_target(self):
        edges = {'a': 'b', 'b': None, 'c': 'outside'}
        def follow(node):
            edge = edges[node]
            if edge is None:
                return ('dead-end', node)
            if edge not in edges:
                return ('unresolved-target', edge)
            return ('visiting', edge)
        self.assertEqual(follow('a'), ('visiting', 'b'))
        self.assertEqual(follow('b'), ('dead-end', 'b'))
        self.assertEqual(follow('c'), ('unresolved-target', 'outside'))
        self.assertNotEqual(follow('b'), follow('c'))


if __name__ == '__main__':
    unittest.main()
