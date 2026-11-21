#!/usr/bin/env python3
from itertools import product
from collections import Counter
axes=range(4)
def bonds(n):
    return [(s,a) for s in product(range(n),repeat=4) for a in axes]
def rotate(b):
    (t,x,y,z),a=b
    return ((t,z,x,y),(0,2,3,1)[a])
def chosen_links(b):
    site,axis=b
    p=tuple(2*v for v in site)
    q=tuple((p[j]+(j==axis))%4 for j in axes)
    return [(p,axis),(q,axis)]
def sort_adjacent(source,target):
    a=list(source); swaps=[]
    for i,v in enumerate(target):
        j=a.index(v,i)
        while j>i:
            a[j-1],a[j]=a[j],a[j-1]
            swaps.append(j-1); j-=1
    assert a==list(target)
    return swaps
def permute(vec,swaps):
    vec=list(vec)
    for j in swaps: vec[j],vec[j+1]=vec[j+1],vec[j]
    return vec
fine=bonds(4); coarse=bonds(2)
assert len(fine)==1024 and len(set(fine))==1024 and len(coarse)==64
rotated=[rotate(b) for b in fine]
assert Counter(rotated)==Counter(fine)
assert all(rotate(rotate(rotate(b)))==b for b in fine)
selected=[b for coarse_bond in coarse for b in chosen_links(coarse_bond)]
assert len(set(selected))==128
spectators=[b for b in fine if b not in set(selected)]
assert len(spectators)==896
target=selected+spectators
assert len(set(target))==1024
r=sort_adjacent(fine,rotated)
p=sort_adjacent(fine,target)
assert len(r)==46592 and len(p)==41792
values=[((i*71)^0x5a5a)%65521 for i in range(1024)]
decoder=dict(zip(fine,values))
assert permute(values,r)==[decoder[b] for b in rotated]
assert permute(values,p)==[decoder[b] for b in target]
assert selected[0]!=selected[1]
print("PASS: 1024 original links; 64 coarse; 128 pairs; 896 spectators")
print("PASS: native C3 swaps=46592; pair/spectator swaps=41792")
print("PASS: arbitrary-value reindex; reverse-pair negative control")
