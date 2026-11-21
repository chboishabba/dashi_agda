"""Exact arithmetic certificate for native 369 incidence and reaction charge.

ATTRIBUTION: The 3x3x3 / 369 geometry and its 54 native edges are pre-existing
DASHI prior art. This checker is assistant-authored verification assistance.
No Rhea source identity, physical parameters or Agda acceptance is inferred.

Orientation: each bond is from low to high coordinate. Incidence B has -1
at its tail, +1 at its head. For arbitrary integer/rational currents J,
1^T B J = 0 exactly. For reaction columns S with z^T S = 0, total
signed charge is conserved by the transport-reaction vector field.
Boundary currents are deliberately an independent input, not suppressed.
"""
from fractions import Fraction
from itertools import product

POINTS = tuple(product((-1, 0, 1), repeat=3))
INDEX = {p: i for i, p in enumerate(POINTS)}
EDGES = tuple(
    (INDEX[p], INDEX[q])
    for p in POINTS
    for axis in range(3)
    if p[axis] < 1
    for q in [tuple(p[k] + (k == axis) for k in range(3))]
)
assert len(POINTS) == 27 and len(EDGES) == 54
assert len(set(EDGES)) == 54


def incidence_columns():
    """Integer columns with one source -1 and one target +1."""
    return tuple(
        tuple((-1 if site == a else 1 if site == b else 0)
              for site in range(27))
        for a, b in EDGES
    )


def transport_divergence(edge_currents):
    """B J for arbitrary 54 x n exact-valued currents."""
    if len(edge_currents) != 54:
        raise ValueError("exactly 54 bond currents required")
    if not edge_currents:
        raise ValueError("missing bond currents")
    species = len(edge_currents[0])
    if species == 0 or any(len(j) != species for j in edge_currents):
        raise ValueError("all edges require the same positive species dimension")
    out = [[Fraction(0) for _ in range(species)] for _ in range(27)]
    for (a, b), j in zip(EDGES, edge_currents):
        for k, value in enumerate(j):
            value = Fraction(value)
            out[a][k] -= value
            out[b][k] += value
    return tuple(tuple(x) for x in out)


def total_species_change(edge_currents):
    div = transport_divergence(edge_currents)
    return tuple(sum((div[i][s] for i in range(27)), Fraction(0))
                 for s in range(len(div[0])))


def signed_charge_change(edge_currents, valences):
    """Exact z^T 1^T B J; valences may be signed."""
    change = total_species_change(edge_currents)
    if len(valences) != len(change):
        raise ValueError("valence dimension mismatch")
    return sum((Fraction(z) * x for z, x in zip(valences, change)),
               Fraction(0))


def stoichiometric_charge_defects(reactants, products, valences):
    """Return z^T S per reaction; never silently accept a charged column."""
    if len(reactants) != len(products):
        raise ValueError("reaction count mismatch")
    n = len(valences)
    if any(len(a) != n or len(b) != n
           for a, b in zip(reactants, products)):
        raise ValueError("species count mismatch")
    return tuple(sum((Fraction(z) * (Fraction(b) - Fraction(a))
                      for a, b, z in zip(ra, pr, valences)),
                     Fraction(0))
                 for ra, pr in zip(reactants, products))


def charge_balance_receipt(edge_currents, valences, reactants,
                           products, reaction_rates, boundary_exchange=None):
    """Exact continuity identity, with boundary flux explicitly recorded.

    For per-site reaction rates v and an optional per-site exchange X,
    dQ/dt = sum_sites sum_reactions v * (z^T S) + sum_sites z^T X.
    Internal 54-bond flux cancels independently. Rates may be rational
    and signed; no numerical solver or biochemical validity is assumed.
    """
    n = len(valences)
    if len(reaction_rates) != 27:
        raise ValueError("reaction rate requires 27 site rows")
    defects = stoichiometric_charge_defects(reactants, products, valences)
    if any(len(row) != len(defects) for row in reaction_rates):
        raise ValueError("reaction-rate column count mismatch")
    if boundary_exchange is None:
        boundary_exchange = [[0] * n for _ in range(27)]
    if len(boundary_exchange) != 27 or any(len(row) != n for row in boundary_exchange):
        raise ValueError("boundary exchange must be 27 x species")
    internal = signed_charge_change(edge_currents, valences)
    reaction = sum((Fraction(rate) * defect
                    for row in reaction_rates
                    for rate, defect in zip(row, defects)), Fraction(0))
    boundary = sum((Fraction(x) * Fraction(z)
                    for row in boundary_exchange
                    for x, z in zip(row, valences)), Fraction(0))
    return {"internal": internal, "reaction": reaction,
            "boundary": boundary, "total": internal + reaction + boundary,
            "column_charge_defects": defects}


def verify_native_incidence():
    columns = incidence_columns()
    assert len(columns) == 54
    assert all(sum(col) == 0 and col.count(-1) == 1 and col.count(1) == 1
               for col in columns)
    assert all(sum(1 for a, b in EDGES if a == site or b == site) == degree
               for site, degree in enumerate(
                   sum(1 for a, b in EDGES if a == i or b == i)
                   for i in range(27)))
    return True


if __name__ == "__main__":
    assert verify_native_incidence()
    print("Native 369 27x54 incidence: exact column cancellation PASS")
