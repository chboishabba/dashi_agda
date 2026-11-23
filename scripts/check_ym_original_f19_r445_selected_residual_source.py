#!/usr/bin/env python3
"""Reference check of ORIGINAL R445 vs F19 target bond labels.

Original source owners:
- BalabanPeriodicTorus4Carrier allCyclicIndices/cartesian bond order
- YMClayNativeSideFourPairDistinctCertificateExact selectedFinePairLabels
- YMClayR445OriginalAxialBondParityInjectiveExact originalR445SelectedFineBond
- YMClayNativeSideFourPairSpectatorSortProgramExact remainingOriginalFineBonds
- YMClayR445CanonicalBondPermutationCodecExact removeSelected
An exact finite positive-bond label audit, not Agda kernel/physical Gibbs proof.
"""
from itertools import product

def step(site, axis, L=4):
    coords=list(site)
    coords[axis]=(coords[axis]+1)%L
    return tuple(coords)

fine=[(site,axis) for site in product(range(4),repeat=4) for axis in range(4)]
coarse=[(site,axis) for site in product(range(2),repeat=4) for axis in range(4)]

def f19_first(bond):
    site,axis=bond
    return tuple(2*x for x in site),axis

def f19_second(bond):
    site,axis=bond
    return step(tuple(2*x for x in site),axis),axis

def r445_selected(bond,parity):
    site,axis=bond
    return tuple(2*x+(parity if i==axis else 0)
                 for i,x in enumerate(site)),axis

def run():
    f19=[b for c in coarse for b in (f19_first(c),f19_second(c))]
    r445=[r445_selected(c,p) for c in coarse for p in (0,1)]
    assert len(f19)==128 and f19==r445
    selected=set(f19)
    suffix_f19=[b for b in fine if b not in selected]
    suffix_r445=[b for b in fine if b not in set(r445)]
    assert len(suffix_f19)==896 and suffix_f19==suffix_r445
    all_bonds=f19+suffix_f19
    assert len(all_bonds)==len(set(all_bonds))==1024
    assert set(all_bonds)==set(fine)
    canonical={b:i for i,b in enumerate(fine)}
    permutation=[canonical[b] for b in all_bonds]
    inverse=[0]*1024
    for i,j in enumerate(permutation): inverse[j]=i
    assert [all_bonds[inverse[i]] for i in range(1024)]==fine
    assert sum(
        (f19_first(c),f19_second(c))==
        (r445_selected(c,0),r445_selected(c,1))
        for c in coarse)==64
    reversed_pair=[b for c in coarse
                   for b in (f19_second(c),f19_first(c))]
    assert sum(x!=y for x,y in zip(f19,reversed_pair))==128
    print("PASS original F19/R445 selected fine-bond labels: 128/128 in source order")
    print("PASS original F19/R445 896-spectator suffix: 896/896 in source order")
    print("PASS 1024/1024 canonical reorder + inverse; every fine bond retained")
    print("PASS actual ordered 64/64 native two-link bond pairs")
    print("NEGATIVE reversed pair order differs: 128/128")
    print("OPEN Agda full 1024-label target-Vec equivalence kernel, physical W1/W3, E1/OS")

if __name__=="__main__":
    run()
