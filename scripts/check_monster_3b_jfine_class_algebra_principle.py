#!/usr/bin/env python3
"""Independent small-group proof-of-principle for the MN3B class-algebra screen.

G=S3 x C4, z=(123,identity), Zclass={z,z^2} has size two.
Verifies class multiplication weights, centralizer order discriminator,
and Z[zeta] phase trace against a genuine degree-two S3 character.
This is NOT a Monster class-data or normalizer-group receipt.
"""
from itertools import permutations,product
from collections import Counter
import json
S=list(permutations(range(3)))
def perm_mul(p,q):return tuple(p[q[i]] for i in range(3))
def perm_inv(p):return tuple(p.index(i) for i in range(3))
def mul(x,y):return perm_mul(x[0],y[0]),(x[1]+y[1])%4
def inv(x):return perm_inv(x[0]),(-x[1])%4
def power(g,k):
    h=e
    for _ in range(k):h=mul(h,g)
    return h
def order(g):return next(k for k in range(1,25) if power(g,k)==e)
def conj(g,h):return mul(mul(inv(h),g),h)
e=((0,1,2),0)
z=((1,2,0),0)
G=[(p,n) for p,n in product(S,range(4))]
assert len(G)==24 and order(z)==3
classes=[];unseen=set(G)
while unseen:
    g=next(iter(unseen));C={conj(g,h) for h in G}
    assert C<=unseen
    classes.append(C);unseen-=C
where={g:i for i,C in enumerate(classes) for g in C}
cz=where[z]
assert classes[cz]=={z,power(z,2)}
def chi(g):
    p=g[0]
    if p==e[0]:return 2
    if p in ((1,2,0),(2,0,1)):return -1
    return 0
assert chi(e)==2 and chi(z)==chi(power(z,2))==-1
number_of_classes_checked=0
centralizing_coprime_classes=0
phase_swappers_rejected=0
for i,C in enumerate(classes):
    counts=Counter(where[mul(t,x)] for t in classes[cz] for x in C)
    for j,n in counts.items():
        assert n%len(classes[j])==0
        c=n//len(classes[j])
        weight=c*len(classes[j])//len(C)
        assert weight*len(C)==c*len(classes[j])
    g=next(iter(C))
    predicted=[]
    for j,n in counts.items():
        predicted.extend([j]*(n//len(C)))
    assert len(predicted)==2
    actual=[where[mul(z,g)],where[mul(power(z,2),g)]]
    assert sorted(predicted)==sorted(actual)
    number_of_classes_checked+=1
    o=order(g)
    if o in (1,2,4):
        preserves=mul(g,z)==mul(z,g)
        order_test=all(order(mul(power(z,t),g))==3*o for t in (1,2))
        assert preserves==order_test
        if preserves:
            triple=[chi(g),chi(mul(z,g)),chi(mul(power(z,2),g))]
            assert triple[1]==triple[2]
            assert (triple[0]-triple[1])%3==0
            projected=(triple[0]-triple[1])//3
            assert projected==1
            centralizing_coprime_classes+=1
        else:phase_swappers_rejected+=1
assert number_of_classes_checked==12
receipt=dict(status='independent exact class-algebra principle passed',
             toy_group='S3 x C4',group_order=len(G),class_count=number_of_classes_checked,
             selected_central_pair_class_size=len(classes[cz]),
             centralizing_coprime_classes=centralizing_coprime_classes,
             phase_swappers_rejected=phase_swappers_rejected,
             mathematical_scope='class-sum weights and phase/order test only, NOT Monster MN3B',
             gap_or_mmgroup_required=False)
print(json.dumps(receipt,indent=2))
