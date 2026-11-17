"""Exact bond-order weld between original Agda native cube and Python PNP solver.

USER PRIOR ART: the original Ternary27Point, PositiveBond and 369 index.
This assistant-authored adapter only reconciles two traversal orders.

Native Agda BiologicalFullCubeIncidenceExact:
    xBonds = [xBond segment y z | segment, y, z]
    yBonds = [yBond x segment z | segment, x, z]
    zBonds = [zBond x y segment | segment, x, y]
with segment = (-1 -> 0), (0 -> 1), and coordinate order (-1,0,1).

Python scripts/reactive_pnp_369.py:
    BONDS = [(p, p+axis) | p lexicographic x,y,z, axis x,y,z]
when valid. Both represent 54 positive-oriented physical bonds; their list
indices differ. Never silently identify a native Agda current Vec 54 with a
Python solver flux matrix without the permutation below.
"""
from fractions import Fraction
from itertools import product

TRITS = (-1, 0, 1)
SEGMENTS = (-1, 0)
POINTS = tuple(product(TRITS, repeat=3))
INDEX = {p: i for i, p in enumerate(POINTS)}

def edge(p, axis):
    q = list(p)
    q[axis] += 1
    return INDEX[p], INDEX[tuple(q)]

SOLVER_EDGES = tuple(
    edge(p, axis) for p in POINTS
    for axis in range(3) if p[axis] < 1
)
AGDA_EDGES = (
    tuple(edge((s, y, z), 0) for s in SEGMENTS for y in TRITS for z in TRITS)
    + tuple(edge((x, s, z), 1) for s in SEGMENTS for x in TRITS for z in TRITS)
    + tuple(edge((x, y, s), 2) for s in SEGMENTS for x in TRITS for y in TRITS)
)
assert len(AGDA_EDGES) == len(SOLVER_EDGES) == 54
assert len(set(AGDA_EDGES)) == 54
assert set(AGDA_EDGES) == set(SOLVER_EDGES)

# Index i of a native Agda bond maps to the corresponding Python index.
SOLVER_INDEX_OF_AGDA = tuple(SOLVER_EDGES.index(e) for e in AGDA_EDGES)
AGDA_INDEX_OF_SOLVER = tuple(AGDA_EDGES.index(e) for e in SOLVER_EDGES)
assert sorted(SOLVER_INDEX_OF_AGDA) == list(range(54))
assert sorted(AGDA_INDEX_OF_SOLVER) == list(range(54))
assert any(i != j for i, j in enumerate(SOLVER_INDEX_OF_AGDA))

def agda_to_solver_flux(agda_current):
    if len(agda_current) != 54:
        raise ValueError("54 Agda bonds required")
    return tuple(agda_current[AGDA_INDEX_OF_SOLVER[i]] for i in range(54))

def solver_to_agda_flux(solver_current):
    if len(solver_current) != 54:
        raise ValueError("54 solver bonds required")
    return tuple(solver_current[SOLVER_INDEX_OF_AGDA[i]] for i in range(54))

def divergence(edge_list, values):
    """Exact signed incidence; each element may be a scalar rational."""
    if len(edge_list) != 54 or len(values) != 54:
        raise ValueError("54 edges and 54 current values required")
    out = [Fraction(0) for _ in range(27)]
    for (a, b), value in zip(edge_list, values):
        out[a] -= Fraction(value)
        out[b] += Fraction(value)
    return tuple(out)

def certify_order_weld():
    # Basis-current equality certifies the full linear identity by linearity.
    for i in range(54):
        native = tuple(1 if k == i else 0 for k in range(54))
        translated = agda_to_solver_flux(native)
        assert sum(translated) == 1
        assert divergence(AGDA_EDGES, native) == divergence(SOLVER_EDGES, translated)
        assert solver_to_agda_flux(translated) == native
    return {
        "native_bonds": 54,
        "basis_checks": 54,
        "permutation_identity": False,
        "divergence_preserving": True,
    }

if __name__ == "__main__":
    print(certify_order_weld())
