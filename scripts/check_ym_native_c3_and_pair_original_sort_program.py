#!/usr/bin/env python3
"""Exact native original 1024-label shared adjacent-sort reference.

Same algorithm as source YMClayNativeC3AdjacentSortProgramExact:
for each desired target, bubble its FIRST remaining match to the head
of the unsorted suffix. Original Product.compose applies SECOND first,
so the adjacent-swap sequence order is essential. Independent Python
REFERENCE, not Agda kernel or Haar measurability.
"""
from itertools import product
from hashlib import sha256

BONDS=[(site,axis) for site in product(range(4),repeat=4)
       for axis in range(4)]
assert len(BONDS)==1024 and len(set(BONDS))==1024

def original_c3(bond):
    (x0,x1,x2,x3),axis=bond
    return ((x0,x3,x1,x2), (0,2,3,1)[axis])

def pair_spectator_target():
    coarse=[(site,axis) for site in product(range(2),repeat=4)
            for axis in range(4)]
    selected=[]
    for site,axis in coarse:
        p=tuple(2*x for x in site)
        q=list(p);q[axis]=(q[axis]+1)%4
        selected.extend([(p,axis),(tuple(q),axis)])
    assert len(selected)==128 and len(set(selected))==128
    rest=[bond for bond in BONDS if bond not in set(selected)]
    assert len(rest)==896
    return selected+rest

def original_sort(source,target):
    assert len(source)==len(target) and set(source)==set(target)
    current=source.copy();word=[]
    for position,desired in enumerate(target):
        i=current.index(desired,position)
        while i>position:
            current[i-1],current[i]=current[i],current[i-1]
            word.append(i-1)
            i-=1
    assert current==target
    return word

def run():
    c3target=[original_c3(bond) for bond in BONDS]
    assert all(original_c3(original_c3(original_c3(b)))==b for b in BONDS)
    c3word=original_sort(BONDS,c3target)
    assert len(c3word)==46592
    assert sha256(','.join(map(str,c3word)).encode()).hexdigest()==(
        'a61adb9c6fe7bbfaa12f9255f8fd0fc139e26991e5c158e0643cfa174eca4dc7')
    pairtarget=pair_spectator_target()
    pairword=original_sort(BONDS,pairtarget)
    assert len(pairword)==41792
    assert sha256(','.join(map(str,[BONDS.index(x) for x in pairtarget])).encode()).hexdigest()==(
        '49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada')
    for target,word in ((c3target,c3word),(pairtarget,pairword)):
        temp=BONDS.copy()
        for index in word:temp[index],temp[index+1]=temp[index+1],temp[index]
        assert temp==target
        for index in reversed(word):temp[index],temp[index+1]=temp[index+1],temp[index]
        assert temp==BONDS
    assert pairtarget[0]!=pairtarget[1]
    assert c3target!=BONDS and pairtarget!=BONDS
    print('PASS: actual 1024-label C3, 46,592 adjacent swaps, C3^3=id')
    print('PASS: actual 128 pair+896 spectator, 41,792 adjacent swaps')
    print('PASS: both stable-sort words, inverse words, hashes and negative controls')
    print('REFERENCE ONLY: Agda closed canonical-label equalities still OPEN')

if __name__=='__main__':run()
