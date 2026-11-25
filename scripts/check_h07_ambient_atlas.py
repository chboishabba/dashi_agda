#!/usr/bin/env python3
"""H07 finite F3^5 marked affine atlas; not continuous or physical gluing."""
from itertools import product, combinations, permutations
from collections import Counter, defaultdict
from math import comb

def require(ok, label):
    if not ok: raise RuntimeError(label)

F=range(3); coords=range(5); marks=tuple(combinations(coords,2)); uv=tuple(product(F,repeat=2))
zero=(0,)*5

def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
def scale(k,a): return tuple(k*x%3 for x in a)
def sub(a,b): return add(a,scale(2,b))
def pack(p,a,b,c):
    # p is the ordered pivot pair, remaining coordinates in ambient order.
    q=[i for i in coords if i not in p]; v=[0]*5; w=v.copy(); o=v.copy()
    v[p[0]]=1; w[p[1]]=1
    for j,i in enumerate(q): v[i]=a[j]; w[i]=b[j]; o[i]=c[j]
    return tuple(v),tuple(w),tuple(o)
def points(v,w,o): return frozenset(add(o,add(scale(i,v),scale(j,w))) for i,j in uv)
def det(v,w,p): i,j=p; return (v[i]*w[j]-v[j]*w[i])%3
def chart(v,w,o,p):
    i,j=p; d=det(v,w,p)
    if not d: return None
    t=scale(d,sub(scale(w[j],v),scale(v[j],w)))
    u=scale(d,sub(scale(v[i],w),scale(w[i],v)))
    z=sub(o,add(scale(o[i],t),scale(o[j],u)))
    return t,u,z

# All actual directions, deduplicated by their nine ambient points.
dirs={}
for p in marks:
    for a,b in product(product(F,repeat=3),repeat=2):
        v,w,o=pack(p,a,b,(0,0,0)); key=points(v,w,o)
        dirs.setdefault(key,(v,w))
require(len(dirs)==1210,'directions')
census=Counter(); pair_count=triple_count=0; marked=0; affine_count=0; rotate_count=0
pairs=Counter(); triples=Counter(); failure=Counter(); stable=0
# For each direction, transition offsets are linear in the input offset.
# Test zero and the three basis offsets, which determine every affine offset.
# Point set tests independently validate these basis cases; count extrapolated
# cosets separately from executed comparisons.
for key,(v,w) in dirs.items():
    valid=[p for p in marks if det(v,w,p)]
    census[len(valid)]+=1
    p0=valid[0]; q=[i for i in coords if i not in p0]
    vv,ww,_=chart(v,w,zero,p0)
    for c in [(0,0,0),(1,0,0),(0,1,0),(0,0,1)]:
        _,_,o=pack(p0,(0,)*3,(0,)*3,c); ambient=points(vv,ww,o)
        charts={p:chart(vv,ww,o,p) for p in valid}
        require(len(ambient)==9,'plane points')
        for p,rep in charts.items():
            require(points(*rep)==ambient,'ambient chart reconstruction')
            for r in marks:
                rr=chart(*rep,r)
                if r not in charts:
                    require(rr is None,'singular pivot guard'); failure[p,r]+=1
                else:
                    require(rr==charts[r],'directed transition'); pair_count+=1
            # Actual cyclic permutation of the last three ambient coordinates.
            rot=lambda x:(x[0],x[1],x[3],x[4],x[2])
            perm=(0,1,4,2,3); r=tuple(sorted(perm[i] for i in p))
            rr=chart(*(rot(x) for x in rep),r)
            require(rr is not None and points(*rr)==frozenset(map(rot,ambient)),'rotation covariance'); rotate_count+=1
            if p==(0,1) and all(rep[1][i] for i in (2,3,4)): stable+=1
        for p,r in combinations(valid,2): pairs[p,r]+=1
        for p,r,t in combinations(valid,3):
            require(chart(*chart(*charts[p],r),t)==charts[t],'triple cocycle'); triples[p,r,t]+=1; triple_count+=1
        marked+=len(valid); affine_count+=1
require((affine_count,marked,stable)==(4840,29160,864),'basis-test census')
require(len(pairs)==45 and len(triples)==120,'nonempty pair/triple overlaps')
print('directions',len(dirs),'planes',affine_count//4*27,'marked',marked//4*27,'stable',stable//4*27)
print('mark multiplicity planes',sorted((k,v*27) for k,v in census.items()))
print('directed transitions incl identity',pair_count,'singular',sum(failure.values()),'triples',triple_count,'rotation',rotate_count)
print('pair overlaps',Counter(v//4*27 for v in pairs.values()),'triple overlaps',Counter(v//4*27 for v in triples.values()))
print('PASS')
