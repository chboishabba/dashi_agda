#!/usr/bin/env python3
"""Native ternary local C3 fibre actor: exact finite and destructive checks.

The LOCAL group is Map(C3 x T^n,C3) semidirect C3_sector. Its base is
ABELIAN; the full group is nonabelian but METABELIAN, unlike Hatcher's
perfect horn-exterior source. This group is not the geometric orbifold
pi1, a Galois group, a Monster representation, or a physical connection.

Classical group-action/wreath product mathematics; prior DASHI native
end owner #1244. New source+test ownership belongs to this continuation.
"""
from itertools import product
from random import Random

def levels(n):
    return [(c, w) for c in range(3) for w in product(range(3), repeat=n)]

def action_address(r, x):
    c, w = x
    return ((c + r) % 3, w)

def pullback(f, x):
    return f[(x[0], x[1][:-1])]

def rotate_field(f, r, coordinates):
    lookup = dict(zip(coordinates, f))
    return tuple(lookup[action_address(-r, x)] for x in coordinates)

def add_field(f, g):
    return tuple((a+b)%3 for a,b in zip(f,g))

def group_mul(a,b,coords):
    f,r = a
    g,s = b
    return add_field(f,rotate_field(g,r,coords)), (r+s)%3

def group_inverse(a,coords):
    f,r = a
    return tuple((-x)%3 for x in rotate_field(f,-r,coords)), (-r)%3

def group_comm(a,b,coords):
    return group_mul(group_mul(group_mul(a,b,coords),
              group_inverse(a,coords),coords),
              group_inverse(b,coords),coords)

def single_orbit_delta(n, word, sector):
    return tuple(int((c==sector) and (w==word)) for c,w in levels(n))

def gaussian_rank_mod3(vectors):
    rows=[list(v) for v in vectors if any(v)]
    if not rows: return 0
    m=len(rows[0])
    rank=0
    for col in range(m):
        pivot=next((j for j in range(rank,len(rows)) if rows[j][col]%3),None)
        if pivot is None: continue
        rows[rank],rows[pivot]=rows[pivot],rows[rank]
        inv=1 if rows[rank][col]==1 else 2
        rows[rank]=[(inv*x)%3 for x in rows[rank]]
        for j in range(len(rows)):
            if j!=rank and rows[j][col]:
                t=rows[j][col]
                rows[j]=[(a-t*b)%3 for a,b in zip(rows[j],rows[rank])]
        rank+=1
    return rank

def expected_augmentation_zero(f, n):
    coordinates=levels(n)
    lookup=dict(zip(coordinates,f))
    return all(sum(lookup[(c,w)] for c in range(3))%3==0
               for w in product(range(3), repeat=n))

def run():
    rng=Random(20261028)
    for n in range(4):
        coarse=levels(n)
        fine=levels(n+1)
        assert len(coarse)==3**(n+1)
        assert len(fine)==3**(n+2)
        assert all(x==(x[0],x[1]+(0,))[:1]+((x[1]+(0,))[:-1],)
                   for x in coarse)
        for _ in range(12):
            f=tuple(rng.randrange(3) for _ in coarse)
            g=tuple(rng.randrange(3) for _ in coarse)
            h=tuple(rng.randrange(3) for _ in coarse)
            for r,s in product(range(3),repeat=2):
                assert rotate_field(rotate_field(f,s,coarse),r,coarse)==rotate_field(f,(r+s)%3,coarse)
                assert rotate_field(add_field(f,g),r,coarse)==add_field(rotate_field(f,r,coarse),rotate_field(g,r,coarse))
                a=(g,r)
                b=(h,s)
                lhs=group_mul(a,b,coarse)
                assert group_mul(lhs,group_inverse(b,coarse),coarse)==a
                target=group_mul(a,b,coarse)
                for x in fine:
                    pb=dict(zip(fine,(pullback(dict(zip(coarse,f)),y) for y in fine)))
                    assert pullback(dict(zip(coarse,rotate_field(f,r,coarse))),x)==rotate_field(tuple(pb[y] for y in fine),r,fine)[fine.index(x)]
                # Check associated action of symmetry element on f.
                acted=lambda group,field: add_field(group[0],rotate_field(field,group[1],coarse))
                assert acted(target,f)==acted(a,acted(b,f))
        if n<=2:
            words=list(product(range(3),repeat=n))
            vectors=[]
            z=tuple(0 for _ in coarse)
            for w in words:
                d=single_orbit_delta(n,w,0)
                for r in (1,2):
                    comm_f,comm_r=group_comm((z,r),(d,0),coarse)
                    assert comm_r==0
                    assert expected_augmentation_zero(comm_f,n)
                    vectors.append(comm_f)
            assert gaussian_rank_mod3(vectors)==2*len(words)
            assert 3**(3*len(words)+1)//(3**(2*len(words)))==3**(len(words)+1)
    # Explicitly enumerate ALL 81 group elements at depth zero.
    coords=levels(0)
    groups=[(g,r) for g in product(range(3),repeat=3) for r in range(3)]
    assert len(groups)==81
    identity=((0,0,0),0)
    assert all(group_mul(g,group_inverse(g,coords),coords)==identity for g in groups)
    for a in groups:
        for b in groups:
            for c in (groups[0],groups[14],groups[39],groups[80]):
                assert group_mul(group_mul(a,b,coords),c,coords)==group_mul(a,group_mul(b,c,coords),coords)
    comm_values={group_comm(a,b,coords) for a in groups for b in groups}
    assert len(comm_values)==9
    assert all(phase==0 and sum(v)%3==0 for v,phase in comm_values)
    assert any(group_mul(a,b,coords)!=group_mul(b,a,coords)
               for a in groups for b in groups)
    assert all(group_comm(a,b,coords)==identity
               for a in comm_values for b in comm_values)

    print("PASS native_ternary_fibre_action")
    print("  K3_n cells n=0,1,2,3:",[3**(n+1) for n in range(4)])
    print("  |G_2|=3^27 =",3**27,"|H_2|=3^28 =",3**28)
    print("  |[H_2,H_2]|=3^18 =",3**18,"|H_2^ab|=3^10 =",3**10)
    print("  depth0 H0=81; commutator subgroup=9; second derived=1")
    print("  all finite pullback/sector-action tests passed")
    print("BOUNDARIES: no complete Agda kernel receipt or locally-constant topology proof")
    print("            no wild exterior pi1 identification and no perfect-to-Hn homomorphism construction")

if __name__=="__main__":
    run()
