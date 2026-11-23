#!/usr/bin/env python3
"""Exact selected Rhea microspecies cut; not native 29x12 or measured kinetics."""
from sympy import Matrix, zeros, symbols, __version__
from build_bh4_stoichiometric_matrix import build_matrix

# ChEBI id, CHNOP counts, signed charge; Rhea web rows observed 2026-11-20.
# QDPR rows match BH4RheaChEBIReactionExact; source bytes/release not pinned.
SPECIES = {
    59560: (9,15,5,3,0,0), 58315: (9,11,1,3,0,0),
    15379: (0,0,0,2,0,0), 15642: (9,15,5,4,0,0),
    57504: (9,11,1,4,0,0), 43120: (9,13,5,3,0,0),
    15377: (0,2,0,1,0,0), 57945: (21,27,7,14,2,-2),
    15378: (0,1,0,0,0,1), 57540: (21,26,7,14,2,-1),
    59905: (8,12,1,2,0,1), 16526: (1,0,0,2,0,0),
    38290: (6,7,0,6,0,-1), 72587: (8,12,1,3,0,1),
    59513: (6,6,0,6,0,-1),
}
# Directed Rhea IDs, signed coefficients (products positive).
REACTIONS = {
    18202: {59560:-1,58315:-1,15379:-1,15642:1,57504:1},
    11921: {15642:-1,43120:1,15377:1},
    32253: {43120:-1,57945:-1,15378:-1,59560:1,57540:1},
    12273: {57504:-1,15378:-1,59905:1,16526:1},
    19118: {59905:-1,38290:-2,15379:-1,72587:1,59513:2,15377:1},
}


def check():
    ids = list(SPECIES)
    A = Matrix([SPECIES[k] for k in ids]).T
    S = Matrix([[r.get(k,0) for r in REACTIONS.values()] for k in ids])
    # Use the existing finite matrix producer, with a distinct web-row schema.
    receipt = {"schema": "dashi.catecholamine-web-row-selection.v1", "reactions": [
        {"rhea_id": f"RHEA:{rid}", "formula_charge_ready": True,
         "participants": [{"chebi_id": f"CHEBI:{k}", "coefficient": abs(n),
                           "side": "product" if n>0 else "substrate"}
                          for k,n in r.items()]} for rid,r in REACTIONS.items()]}
    native = build_matrix(receipt)
    assert not native["finite_formula_residuals"]
    assert native["finite_species_count"] == 15 and native["finite_reaction_count"] == 5
    ordered = Matrix(native["matrix"]).extract(
        [native["species_index"].index(f"CHEBI:{k}") for k in ids],
        [native["reaction_index"].index(f"RHEA:{r}") for r in REACTIONS])
    assert ordered == S
    col = lambda d: Matrix([d.get(k,0) for k in ids])
    assert A*S == zeros(6,5)
    pterins = [ids.index(k) for k in (59560,15642,43120)]
    P = S.extract(pterins,range(5))
    assert Matrix([[1,1,1]])*P == zeros(1,5)
    assert P*Matrix([1,1,1,0,0]) == zeros(3,1)
    assert S*Matrix([1,1,1,1,0]) == col({58315:-1,15379:-1,57945:-1,15378:-2,57540:1,15377:1,59905:1,16526:1})
    assert S*Matrix([1,1,1,1,1]) == col({58315:-1,15379:-2,57945:-1,15378:-2,57540:1,15377:2,16526:1,38290:-2,72587:1,59513:2})
    t,p,q,d,b = symbols('t p q d b')
    v = Matrix([t,p,q,d,b]); delta = S*v
    row = lambda k: delta[ids.index(k)]
    assert row(59905) == d-b and row(72587) == b
    assert row(57504) == t-d and row(57945) == -q
    # At zero pterin and DOPA accumulation, TH=PCD=QDPR=DDC.
    assert P.rank() == 2
    K = S.extract(pterins+[ids.index(57504)],range(5))
    assert K.nullspace() == [Matrix([1,1,1,1,0]),Matrix([0,0,0,0,1])]
    # Distinct histories: same DA/NE delta, different turnover and DOPA.
    v1,v2 = Matrix([1,1,1,1,0]), Matrix([2,2,2,1,0])
    O = S.extract([ids.index(59905),ids.index(72587)],range(5))
    assert O*v1 == O*v2 == Matrix([1,0])
    assert (S*v2-S*v1)[ids.index(57504)] == 1
    assert (S*v2-S*v1)[ids.index(57945)] == -1
    # Negative controls: missing proton, ROS radical coefficient, no QDPR.
    assert A*(S[:,3]+col({15378:1})) != zeros(6,1)
    assert A*(S[:,4]+col({59513:-1})) != zeros(6,1)
    assert P*Matrix([1,1,0,0,0]) != zeros(3,1)
    # Executable availability: both schedules share identical starting stocks.
    # Start with the reactants needed for both schedules, one BH4 recycled twice.
    initial=col({59560:1,58315:2,15379:2,57945:2,15378:3})
    def run(seq):
        x=initial.copy()
        for j in seq:
            assert all(x[i]>=max(0,-S[i,j]) for i in range(len(ids)))
            x += S[:,j]
            assert all(a>=0 for a in x)
        return x-initial
    assert run([0,1,2,3]) == S*v1
    assert run([0,1,2,0,1,2,3]) == S*v2
    # Stoichiometry alone does not imply the omitted sinks are physically zero.
    print(f'SymPy {__version__}: 30/30 CHNOP/net-charge entries zero; 2 exact net paths;')
    print('pterin invariant, rank/nullspace, 2 feasible histories, 3 negative controls PASS')
    print('Native builder: exact 75/75 coefficient agreement')
    print('Selected species:', len(ids), 'reaction rank:', S.rank(), 'observer rank:', O.rank())


if __name__ == '__main__':
    check()
