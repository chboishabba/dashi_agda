"""Concrete Golay parity/glue Leech presentation in integer coordinates / sqrt(8).

Classical construction: Conway--Sloane, Sphere Packings, Lattices and Groups;
see R. A. Wilson, Finite Simple Groups, section 5.3:
https://webspace.maths.qmul.ac.uk/r.a.wilson/FSG/notes5.pdf
and M. Seysen, A fast implementation of the Monster group,
doi:10.1016/j.jaca.2024.100012.
DASHI supplies executable exact membership, basis, inverse and move receipts.
This is not the original neural model, a three-E8 isometry or a Co0 enumeration.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

N = 24
ALL = (1 << N) - 1
G = sum(1 << i for i in (11,9,7,6,5,1,0))
GENERATORS = tuple((G << i) | (((G << i).bit_count() % 2) << 23)
                   for i in range(12))


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


@lru_cache(maxsize=1)
def golay():
    code = {0}
    for g in GENERATORS:
        code |= {c ^ g for c in code}
    require(Counter(c.bit_count() for c in code) ==
            {0:1,8:759,12:2576,16:759,24:1}, 'invalid Golay code')
    require(ALL in code and all((a & b).bit_count()%2 == 0
                for a in GENERATORS for b in GENERATORS),
            'Golay self-duality check failed')
    return frozenset(code)


def membership(point):
    x = tuple(point)
    require(len(x) == N and all(type(v) is int for v in x),
            'integer coordinate24 required')
    m = x[0] % 2
    if any(v%2 != m for v in x):
        return None
    c = sum(((v-m)//2%2)<<i for i,v in enumerate(x))
    if c not in golay() or sum(x)%8 != 4*m:
        return None
    return dict(parity=m, golay_mask=c, sum_mod8=sum(x)%8,
                integer_norm_squared=sum(v*v for v in x))


def generator_columns():
    # 4D24: all multiples of 4 whose coordinate sum is 0 mod 8.
    columns = [tuple(4*int(j==i)-4*int(j==23) for j in range(N))
               for i in range(23)]
    columns.append(tuple(8*int(j==23) for j in range(N)))
    columns.extend(tuple(2*((g>>j)&1) for j in range(N))
                   for g in GENERATORS)
    # Odd coset, 2*odd is in the even sublattice via all-ones code.
    columns.append((-3,)+(1,)*23)
    require(all(membership(v) for v in columns), 'generator lacks membership')
    return tuple(columns)


@lru_cache(maxsize=1)
def basis():
    from sympy import Matrix
    from sympy.matrices.normalforms import hermite_normal_form
    b = hermite_normal_form(Matrix(generator_columns()).T)
    require(b.shape == (N,N) and abs(b.det()) == 2**36,
            'wrong integer covolume')
    gram = b.T*b/8
    require(all(v.q==1 for v in gram) and
            all(gram[i,i]%2==0 for i in range(N)) and gram.det()==1,
            'not an even unimodular Gram matrix')
    # The membership rule has index 2^(49-12-1)=2^36:
    # 4D24 index 2^49, 4096 even code cosets, two parity cosets.
    # Closure follows from the residue arithmetic and doubly-even code.
    # Hence the contained basis span equals the membership rule.
    require(all(membership(tuple(map(int,b[:,j]))) for j in range(N)),
            'basis column membership failure')
    return b.as_immutable()


@lru_cache(maxsize=1)
def basis_inverse():
    return basis().inv().as_immutable()


def from_coordinates(coords):
    from sympy import Matrix
    coords = tuple(coords)
    require(len(coords)==N and all(type(v) is int for v in coords),
            'integer lattice basis coordinates required')
    return tuple(map(int,basis()*Matrix(coords)))


def to_coordinates(point):
    from sympy import Matrix
    point = tuple(point)
    require(membership(point) is not None, 'not a Leech lattice member')
    a = basis_inverse()*Matrix(point)
    require(all(v.q==1 for v in a), 'membership not in generated lattice')
    coords = tuple(map(int,a))
    require(from_coordinates(coords)==point, 'lattice basis inverse failed')
    return coords


def translate(point, displacement):
    a = tuple(point); b = tuple(displacement)
    require(membership(a) is not None and membership(b) is not None,
            'both point and move must be certified members')
    target = tuple(x+y for x,y in zip(a,b))
    require(membership(target) is not None, 'lattice addition failed')
    return target


def signed_action(point, mask):
    require(type(mask) is int and mask in golay(), 'sign mask not Golay')
    return tuple(-x if (mask>>i)&1 else x for i,x in enumerate(point))


def cycle_action(point):
    return (point[22],)+tuple(point[:22])+(point[23],)


def minimum_vectors():
    # Norm 32 before scaling. These disjoint families exhaust the
    # nonzero norm-32 cases by parity and minimum Golay weight 8.
    for i,j in combinations(range(N),2):
        for a,b in product((-4,4),repeat=2):
            x = [0]*N; x[i]=a; x[j]=b
            yield 'two_four',tuple(x)
    for mask in sorted(golay()):
        if mask.bit_count()!=8:
            continue
        support = [i for i in range(N) if (mask>>i)&1]
        for signs in range(128):
            signs |= (signs.bit_count()%2)<<7
            x = [0]*N
            for j,i in enumerate(support):
                x[i] = -2 if (signs>>j)&1 else 2
            yield 'octad',tuple(x)
    for mask in sorted(golay()):
        unit = tuple(-1 if (mask>>i)&1 else 1 for i in range(N))
        for j in range(N):
            x = list(unit); x[j] *= -3
            yield 'odd',tuple(x)


def certificate(enumerate_shell=False):
    b = basis()
    cols = [tuple(map(int,b[:,j])) for j in range(N)]
    # Exact BIDI and additive moves on actual basis; no ambient flips.
    for j,v in enumerate(cols):
        require(to_coordinates(v)==tuple(int(i==j) for i in range(N)),
                'basis unit inverse failed')
        require(translate(v,tuple(-x for x in v))==(0,)*N,
                'move inverse failed')
    # Each action is an isometry and invertible with explicit finite
    # order; preserving generators implies preserving the entire lattice.
    for mask in GENERATORS:
        for v in cols:
            target = signed_action(v,mask)
            require(membership(target) is not None and
                    signed_action(target,mask)==v, 'sign action failed')
            to_coordinates(target)
    for v in cols:
        target = cycle_action(v)
        require(membership(target) is not None, 'cycle action failed')
        to_coordinates(target)
        for _ in range(22):
            target=cycle_action(target)
        require(target==v, 'cycle inverse failed')
    # A norm-16 even vector is either one +/-4 (sum glue rejects)
    # or four +/-2 (code weight 4 rejects). Odd norm is at least 24.
    require(all(membership(tuple(4*int(i==j) for i in range(N))) is None
                for j in range(N)), 'ambient bit probe admitted')
    require(min(c.bit_count() for c in golay() if c)==8,
            'rootlessness code bound failed')
    expected = {'two_four':4*276,'octad':759*128,'odd':4096*24}
    actual = None
    if enumerate_shell:
        counts = Counter()
        seen = set()
        for family,x in minimum_vectors():
            m = membership(x)
            require(m is not None and m['integer_norm_squared']==32,
                    'invalid minimum vector')
            require(x not in seen, 'duplicate minimum vector')
            seen.add(x); counts[family]+=1
        require(counts==expected, 'minimum shell enumeration mismatch')
        actual = dict(counts)
    return dict(
        construction='Golay parity/glue integer coordinate24 divided by sqrt(8)',
        golay_weight_distribution=dict(Counter(c.bit_count() for c in golay())),
        integer_basis_columns=cols,
        integer_basis_determinant=abs(int(b.det())),
        normalized_gram_determinant=1, even_integral_gram=True,
        rootlessness_norm16_exclusion=True,
        minimum_squared_norm=4,
        minimum_shell_family_counts=expected,
        minimum_shell_count=sum(expected.values()),
        minimum_shell_enumerated=enumerate_shell, enumerated_counts=actual,
        certified_basis_coordinate_roundtrip=True,
        generator_sign_flips_and_cyclic_permutation_preserve_lattice=True,
        ambient_single_coordinate_flip_admitted=False,
        three_e8_direct_sum_isometry_claimed=False,
        three_e8_source_glue_isometry_constructed=False,
        original_neural_history_membership_claimed=False,
        full_conway_group_certified=False, agda_kernel_checked=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--enumerate-shell',action='store_true')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    result=json.dumps(certificate(a.enumerate_shell),sort_keys=True,indent=2)+'\n'
    if a.output:
        a.output.write_text(result)
    print(result,end='')


if __name__=='__main__':
    main()
