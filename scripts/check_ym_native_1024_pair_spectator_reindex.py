#!/usr/bin/env python3
"""Exact selected native 1024 positive-bond reindex plan for side4->side2.

Independent Python reference ONLY: not a closed Agda LinkPermutation program,
no continuous compact SU(N) Haar or physical Gibbs-disintegration proof.
"""
from itertools import product
from hashlib import sha256

fine=[(s,a) for s in product(range(4),repeat=4) for a in range(4)]
coarse=[(s,a) for s in product(range(2),repeat=4) for a in range(4)]
selected=[]
for s,a in coarse:
    p=tuple(2*x for x in s)
    q=list(p);q[a]=(q[a]+1)%4
    selected.extend([(p,a),(tuple(q),a)])
assert len(fine)==1024 and len(set(fine))==1024
assert len(coarse)==64 and len(selected)==128 and len(set(selected))==128
lookup={bond:i for i,bond in enumerate(fine)}
selected_set=set(selected)
spectators=[bond for bond in fine if bond not in selected_set]
assert len(spectators)==896
order=[lookup[bond] for bond in selected+spectators]
assert sorted(order)==list(range(1024))
inverse=[0]*1024
for new,old in enumerate(order): inverse[old]=new
assert all(order[inverse[i]]==i for i in range(1024))
assert all(inverse[order[i]]==i for i in range(1024))

arr=list(range(1024))
swaps=[]
for dest,origin in enumerate(order):
    at=arr.index(origin)
    while at>dest:
        arr[at-1],arr[at]=arr[at],arr[at-1]
        swaps.append(at-1)
        at-=1
assert arr==order
assert all(0<=i<=1022 for i in swaps)
assert swaps and list(range(1024))!=order
# Negative controls: duplicate element invalid; wrong pair-order is not same block.
bad=order.copy();bad[1]=bad[0]
assert sorted(bad)!=list(range(1024))
bad=order.copy();bad[0],bad[1]=bad[1],bad[0]
assert bad!=order and sorted(bad)==list(range(1024))
assert len(swaps)==41792
digest=sha256(','.join(map(str,order)).encode()).hexdigest()
assert digest=='49b954c21ccd1649208074eb5096e5b6b63102313da773fe17e1268b67727ada'
print('PASS: original 4D 1024 bonds: 128 pair-selected and 896 spectator')
print('PASS: forward/inverse permutation, 41,792 adjacent swaps, negative controls')
print('adjacent_swap_count=',len(swaps))
print('permutation_sha256=',digest)
print('REFERENCE ONLY: next step is Agda LinkPermutation and canonical label-vector proof')
