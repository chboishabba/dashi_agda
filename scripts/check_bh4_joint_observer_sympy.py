#!/usr/bin/env python3
"""Selected reaction/transfer observer: exact algebra, not calibrated kinetics."""
from itertools import combinations
from sympy import Matrix, eye, ones, zeros, kronecker_product, __version__
from check_bh4_catecholamine_sympy import SPECIES, REACTIONS
from reactive_pnp_369 import POINTS, BONDS


def check():
    ids = list(SPECIES)
    keys = [(c,k) for c in 'CVE' for k in ids]
    def col(entries):
        return Matrix([entries.get(k,0) for k in keys])
    def unit(c,k):
        return col({(c,k):1})
    # TH/PCD/QDPR/DDC cytosolic; DBH vesicular: selected topology only.
    R = Matrix.hstack(*(col({(c,k):n for k,n in r.items()})
                       for c,r in zip('CCCCV',REACTIONS.values())))
    # TransferStep order: packing, exocytosis, efflux, reuptake, C/E loss.
    T = Matrix.hstack(*(v for k in (59905,72587) for v in (
        unit('V',k)-unit('C',k), unit('E',k)-unit('V',k),
        unit('E',k)-unit('C',k), unit('C',k)-unit('E',k),
        -unit('C',k), -unit('E',k))))
    M = R.row_join(T)
    A = Matrix([SPECIES[k] for c,k in keys]).T
    assert A*R == zeros(6,5)
    internal = [0,1,2,3,6,7,8,9]
    assert A*T[:,internal] == zeros(6,8)
    # Losses are boundary exports of intact molecular inventory, not decay chemistry.
    L = T[:,[4,5,10,11]]
    assert A*L == -Matrix([SPECIES[k] for k in (59905,59905,72587,72587)]).T
    endpoint = M[[keys.index(('E',k)) for k in (59905,72587)],:]
    assert (M.rank(), len(M.nullspace()), endpoint.rank(), len(endpoint.nullspace())) == (11,6,2,15)
    # All stocks still cannot see a directed circulation or the loss-location ambiguity.
    cycles = []
    for offset in (5,11):
        for values in ([1,1,0,1,0,0],[0,0,1,1,0,0],[0,0,1,0,-1,1]):
            # Third vector: C->E plus E loss minus C loss.
            v = zeros(17,1)
            v[offset:offset+6,0] = Matrix(values)
            cycles.append(v)
    assert all(M*v == zeros(45,1) for v in cycles)
    assert Matrix.hstack(*cycles).rank() == 6
    target = eye(17)[:5,:]
    assert all(target*v == zeros(5,1) for v in M.nullspace())
    # Unknown losses/transport do not contribute to these non-monoamine rows.
    candidates = [('C',k) for k in (59560,15642,43120,57504,58315,57945,57540,16526)] + [('V',59513)]
    rows = [M[keys.index(k),:] for k in candidates]
    # exhaustive cardinality-minimal panels restricted to the declared row menu.
    good = []
    for subset in combinations(range(len(rows)),5):
        Q = Matrix.vstack(*(rows[i] for i in subset))
        if Q[:,:5].rank() == 5:
            good.append(tuple(candidates[i] for i in subset))
    assert good and all(row[:,5:] == zeros(1,12) for row in rows)
    # E endpoints supply no reaction-only information with free transport.
    assert endpoint[:,5:].rank() == 2
    chosen = [('C',58315),('C',15642),('C',57945),('C',16526),('V',59513)]
    H = Matrix.vstack(*(M[keys.index(k),:] for k in chosen))
    assert H[:,:5].det() != 0 and H[:,5:] == zeros(5,12)
    assert H[:,:5].inv()*H == target
    # Time-indexed positive history: a silent gross release/reuptake cycle in DA.
    x0=unit('C',59905)*2+unit('V',59905)*2+unit('E',59905)*2
    def evolve(seq):
        x=x0.copy()
        for j in seq:
            c=M[:,j]
            assert all(x[i]>=max(0,-c[i]) for i in range(45))
            x+=c
        return x
    assert evolve([])==evolve([5,6,8])==evolve([7,8])==x0
    # Same full sampled stock at every interval; different gross exocytosis.
    assert all(evolve([5,6,8]*n)==x0 for n in range(1,9))
    # Arbitrary unpaid exchange defeats reaction identification, even all stocks.
    J = M.row_join(eye(45))
    witness = eye(17)[:,0].col_join(-M[:,0])
    assert J*witness == zeros(45,1) and witness[0] == 1
    # Native ordered 369 graph, independent spatial aggregation; no physical C/V/E embedding.
    B=zeros(len(POINTS),len(BONDS))
    for j,(a,b) in enumerate(BONDS):
        B[a,j],B[b,j]=-1,1
    assert ones(1,27)*B==zeros(1,54) and B.rank()==26
    assert len(B.nullspace())==28
    assert kronecker_product(ones(1,27),eye(45))*kronecker_product(B,eye(45))==zeros(45,54*45)
    print(f'SymPy {__version__}: M rank 11/nullity 6; extracellular rank 2/nullity 15')
    print(f'Five-row reaction panels: {len(good)}/126; chosen reconstruction, cycle basis, 8 sampled histories PASS')
    print('Native 369 incidence rank 26/nullity 28; 54 column sums and 45-species aggregate cancellation PASS')


if __name__ == '__main__':
    check()
