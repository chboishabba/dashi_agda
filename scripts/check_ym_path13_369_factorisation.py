import sympy as s
from itertools import product
from collections import Counter
from math import comb
# Coordinate-level pointed orientation codec, not a group map.
X=list(product((-1,0,1),repeat=3)); z=(0,0,0)
R=sorted(x for x in X if x!=z and next(a for a in x if a)!=-1)
assert len(R)==13
assert Counter(sum(a!=0 for a in x) for x in R)=={1:3,2:6,3:4}
enc={x:i-6 for i,x in enumerate(R)}
assert set(enc.values())==set(range(-6,7))
assert all(R[enc[x]+6]==x for x in R)
# A representative codec does not preserve path adjacency (degrees differ).
D=Counter(sum(sum(abs(a-b) for a,b in zip(x,y))==1 for y in X) for x in X)
assert D[6]==1
# Tensor average and detail, exact rational projector laws.
I=s.eye(13); P=s.ones(13)/13; H=I-P
assert P*P==P and H*H==H and P*H==s.zeros(13)
assert P.rank()==1 and H.rank()==12
for d in (3,4):
 ranks=[comb(d,k)*12**k for k in range(d+1)]
 assert sum(ranks)==13**d
 mart=[12*13**(d-k-1) for k in range(d)]
 assert sum(mart)+1==13**d
 print(d,'ANOVA',ranks,'martingale',mart)
assert 4*13**3==8788 and 12*13**4==342732
assert 9*3**9==3**11 and 3**12*3==3**13
print('PASS exact carrier codec, projector identities, tensor ranks and relative scale arithmetic')
