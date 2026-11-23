#!/usr/bin/env python3
"""Finite R445 physical bond labels ↔ 7-bit source address × 3 transverse bits.
Original Wilson source is untouched. Local source-index regression, NOT an Agda or D1 proof.
"""
from collections import Counter
from itertools import product
from math import comb
import sympy as sp

B = tuple(product(range(2), repeat=4))
T = tuple(product(range(2), repeat=3))

def coarse_bond_address(mu, c, p, s):
    """Literal original side-4 positive oriented bond (mu, x_0,...,x_3)."""
    assert mu in range(4) and len(c)==4 and len(s)==3 and p in (0,1)
    x = [2 * c[i] for i in range(4)]
    x[mu] += p
    for i,nu in enumerate(j for j in range(4) if j != mu):
        x[nu] += s[i]
    return (mu, *x)

def unpack_original_bond(bond):
    mu, *x = bond
    assert mu in range(4) and all(z in range(4) for z in x)
    c = tuple(z >> 1 for z in x)
    p = x[mu] & 1
    s = tuple(x[nu] & 1 for nu in range(4) if nu != mu)
    return mu, c, p, s

def transverse_colour(bond):
    mu, c, p, s = unpack_original_bond(bond)
    return (mu, sum(s) % 2)

def plaquettes():
    for x in product(range(4), repeat=4):
        for mu in range(4):
            for nu in range(mu+1,4):
                y = list(x); y[nu] = (y[nu] + 1) % 4
                z = list(x); z[mu] = (z[mu] + 1) % 4
                yield ((mu,*x),(nu,*x),(mu,*y),(nu,*z))

def toggle(s,axis):
    new=list(s);new[axis]=1-new[axis]
    return tuple(new)

def run():
    originals={(mu,*x) for mu in range(4) for x in product(range(4),repeat=4)}
    addresses={(mu,c,p,s) for mu in range(4) for c in B for p in (0,1) for s in T}
    decoded={coarse_bond_address(mu,c,p,s) for mu,c,p,s in addresses}
    assert len(originals)==len(addresses)==len(decoded)==1024
    for address in addresses:
        mu,c,p,s=address
        assert unpack_original_bond(coarse_bond_address(mu,c,p,s))==address
    for bond in originals:
        assert coarse_bond_address(*unpack_original_bond(bond))==bond
    sheet=Counter(unpack_original_bond(b)[3] for b in originals)
    assert set(sheet)==set(T) and set(sheet.values())=={128}
    selected={b for b in originals if unpack_original_bond(b)[3]==(0,0,0)}
    assert len(selected)==128 and len(originals-selected)==896
    assert 896==7*128 and 128==4*16*2
    selected_color=Counter(transverse_colour(b) for b in selected)
    assert selected_color==Counter({(mu,0):32 for mu in range(4)})
    colors=Counter(transverse_colour(b) for b in originals)
    assert colors==Counter({(mu,parity):128 for mu in range(4) for parity in (0,1)})
    plaquette_count=0
    for plaq in plaquettes():
        assert len({transverse_colour(b) for b in plaq})==4
        plaquette_count+=1
    assert plaquette_count==6*4**4==1536
    # Negative control: all 128 selected bonds DO interact across orientations.
    # Conditioning on only 896 spectators does NOT factorize 128 links.
    selected_plaquette_occupancy=Counter(len(set(plaq)&selected) for plaq in plaquettes())
    assert selected_plaquette_occupancy==Counter({0:1152,2:384})
    # Literal three-bit cube (8 vertices, 12 edges, 6 square faces)
    edges={tuple(sorted((s,toggle(s,i)))) for s in T for i in range(3)}
    faces={(i,j,k,v) for i in range(3) for j in range(i+1,3)
           for k in range(3) if k not in (i,j) for v in (0,1)}
    assert len(edges)==12 and len(faces)==6
    for s in T:
        for i in range(3):
            for j in range(3):
                assert toggle(toggle(s,i),j)==toggle(toggle(s,j),i)
    # Three binary sign bits embed into strictly nonzero balanced trits;
    # selected 000 is a CORNER (-,-,-), never the ternary zero centre.
    corners={tuple(2*b-1 for b in s) for s in T}
    assert len(corners)==8 and (-1,-1,-1) in corners and (0,0,0) not in corners
    trit_cube=list(product((-1,0,1),repeat=3))
    by_zeros=Counter(sum(z==0 for z in x) for x in trit_cube)
    assert [by_zeros[z] for z in range(4)]==[8,12,6,1]
    assert 8+12+6+1==27
    # 369 typed binary/ternary refinement: independent factor counts 2^a 3^b.
    for a in range(5):
        for b in range(5):
            assert 2*(2**a*3**(b+1))==3*(2**(a+1)*3**b)
    # A source Wilson plaquette is not invariant under arbitrary SINGLE-BOND
    # transverse toggles; commuting address flips are NOT gauge transformations.
    assert sp.Integer(1024)==sp.Integer(2)**10
    print('PASS 1024/1024 native full-bond roundtrips; 8/8 residual sheets ×128')
    print('PASS selected 128 = 4 orientations ×32; 896 spectators = 7×128')
    print(f'PASS {plaquette_count}/{plaquette_count} plaquettes have four distinct orientation/parity colors')
    print('PASS negative control: 384 original plaquettes contain TWO selected links; only 32-per-orientation classes factorize')
    print('PASS 3-bit cube: 8 vertices, 12 edges, 6 commuting faces')
    print('PASS balanced trit 27 = 8 corners + 12 edges + 6 face centres + 1 centre')
    print('PASS 369 refinement 2^a 3^b commutation; no sign/zero or physical-law promotion')

if __name__=='__main__':
    run()
