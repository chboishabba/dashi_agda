#!/usr/bin/env python3
"""MG06 exact source-geometry test: original 4D YM R445 block and reflection.

Master owners: BalabanPeriodicTorus4Carrier, YMClaySUNNativeBlockedPositiveHolonomyExact,
YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact,
YMClayOriginalWilsonNativeOSPullbackExact.NativeBlockReflectsExactly.
Original R445 native block is an ORDERED length-two positive-link holonomy
from even-coarse sites. The fine site reflection t -> 2-t (mod 4)
preserves those even origins and descends to the side-two reflection.

Free-group words on the 1024 native oriented links prove the identities
for ANY group-valued links, not a numerically selected commuting example.
This is a *geometry and Wilson-real-trace* fixture. It does NOT prove
the Agda NativeBlockReflectsExactly term, physical half-space support,
the actual Gibbs reflection-positive measure, continuum OS or the YM gap.
"""
from itertools import product, combinations

DIM=4

def add(x,axis,n):
    y=list(x); y[axis]=(y[axis]+1)%n; return tuple(y)

def sub(x,axis,n):
    y=list(x); y[axis]=(y[axis]-1)%n; return tuple(y)

def ref(x,n):
    y=list(x); y[0]=(n//2-y[0])%n; return tuple(y)

def word(x,axis):
    return (((x,axis),1),)

def inv(seq):
    return tuple((bond,-sign) for bond,sign in reversed(seq))

def reduce(seq):
    out=[]
    for token in seq:
        if out and out[-1][0]==token[0] and out[-1][1]==-token[1]:
            out.pop()
        else: out.append(token)
    return tuple(out)

def mul(*seqs):
    return reduce(token for seq in seqs for token in seq)

def pulled_link(x,axis):
    image=ref(x,4)
    return inv(word(sub(image,0,4),0)) if axis==0 else word(image,axis)

def block(x,axis):
    origin=tuple(2*t for t in x)
    return mul(word(origin,axis),word(add(origin,axis,4),axis))

def reflected_coarse_block(x,axis):
    image=ref(x,2)
    return inv(block(sub(image,0,2),axis)) if axis==0 else block(image,axis)

def blocked_reflected_fine(x,axis):
    origin=tuple(2*t for t in x)
    return mul(pulled_link(origin,axis),pulled_link(add(origin,axis,4),axis))

def plaquette(x,i,j,link):
    return mul(link(x,i),link(add(x,i,4),j),
               inv(link(add(x,j,4),i)),inv(link(x,j)))

def real_trace_equivalent(a,b):
    # Cyclic conjugation and reversal preserve Re Tr for unitary SU(N).
    a=reduce(a);b=reduce(b)
    if len(a)!=len(b):return False
    for target in (b,inv(b)):
        for index in range(len(target)):
            if a==target[index:]+target[:index]:return True
    return False

def check():
    fine_sites=list(product(range(4),repeat=DIM))
    coarse_sites=list(product(range(2),repeat=DIM))
    coarse_bonds=list(product(coarse_sites,range(DIM)))
    assert len(fine_sites)==256 and 4*len(fine_sites)==1024
    assert len(coarse_sites)==16 and len(coarse_bonds)==64
    assert all(ref(ref(x,4),4)==x for x in fine_sites)
    assert all(ref(ref(x,2),2)==x for x in coarse_sites)
    for x,axis in coarse_bonds:
        assert blocked_reflected_fine(x,axis)==reflected_coarse_block(x,axis),(x,axis)
    count=0
    for x in fine_sites:
        for i,j in combinations(range(DIM),2):
            target=ref(x,4)
            if i==0 or j==0: target=sub(target,0,4)
            assert real_trace_equivalent(
                plaquette(x,i,j,pulled_link),plaquette(target,i,j,word)),(x,i,j)
            count+=1
    assert count==6*len(fine_sites)==1536
    # Wrong link-plane reflection t->3-t maps selected even origins to odd.
    assert (3-0)%4%2==1
    print('PASS original 4D side-four: 256 sites, 1024 positive bonds, 1536 plaquettes')
    print('PASS R445 non-Abelian two-link block commutes with site reflection 64/64')
    print('PASS all original Wilson plaquette real traces transform correctly 1536/1536')
    print('PASS even-origin geometry, side-two reflection and wrong-plane distinction')
    print('OPEN Agda exact-source theorem, positive half-space, real Wilson RP, continuum and OS gap')

if __name__=='__main__':check()
