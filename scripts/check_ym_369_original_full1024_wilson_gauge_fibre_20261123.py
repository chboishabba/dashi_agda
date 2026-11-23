#!/usr/bin/env python3
"""Original 4D Wilson full 1024-link -> 369 signed 9-trit lifted-incidence check.

Finite Q8 <= SU(2) exact group fixture.  This is a SOURCE GEOMETRY/
reindexing regression, not continuous SU(N) Haar, CMP119 T, RP or Clay gap.
The original 4D source site is retained as a fibre over the signed chart;
otherwise the 32 doubled odd midpoints lose independent local gauge actions.
"""
from collections import defaultdict
from itertools import product

units = ((0,1,2,3),(1,0,3,2),(2,3,0,1),(3,2,1,0))
signs = ((1,1,1,1),(1,-1,1,-1),(1,-1,-1,1),(1,1,-1,-1))
def mul(a,b):
    sa,ua=divmod(a,4); sb,ub=divmod(b,4)
    return units[ua][ub]+4*((sa+sb+(signs[ua][ub]<0))%2)
def inv(a):
    return (0,5,6,7,4,1,2,3)[a]
assert all(mul(a,inv(a))==mul(inv(a),a)==0 for a in range(8))
assert all(mul(mul(a,b),c)==mul(a,mul(b,c)) for a,b,c in product(range(8),repeat=3))
assert mul(1,2)!=mul(2,1)

def step(site,axis,n=1):
    vals=list(site); vals[axis]=(vals[axis]+n)%4
    return tuple(vals)
def coarse_base(coarse): return tuple(2*x for x in coarse)
def pair(coarse,axis):
    base=coarse_base(coarse)
    return ((base,axis),(step(base,axis),axis))
def sign9(site): return tuple((-1,0,1,0)[v] for v in site)+(0,)*5
def lifted_vertex(site): return (sign9(site),site)
def lifted_bond(bond):
    s,d=bond
    return (lifted_vertex(s),lifted_vertex(step(s,d)),d,bond)
def gauge(site):
    odd=[x for x in site if x%2]
    if len(odd)==1:return 1 if odd[0]==1 else 2
    return (3+sum((i+2)*x for i,x in enumerate(site)))%8

def plaquette(s,mu,nu):
    s_mu=step(s,mu); s_nu=step(s,nu)
    return ((s,mu,True),(s_mu,nu,True),(s_nu,mu,False),(s,nu,False))
def word_value(word,link):
    val=0
    for s,d,forward in word:
        v=link[(s,d)]
        val=mul(val,v if forward else inv(v))
    return val

def field_value(bond):
    s,d=bond
    # Noncommuting i,j on all original selected R445 pair limbs.
    others=tuple(s[j] for j in range(4) if j!=d)
    if all(x%2==0 for x in others):return 1 if s[d]%2==0 else 2
    return (1+sum((i+3)*x for i,x in enumerate(s))+d*3)%8

def transform(field,g):
    return {(s,d):mul(mul(g(s),value),inv(g(step(s,d))))
            for (s,d),value in field.items()}

sites=list(product(range(4),repeat=4))
coarse_sites=list(product(range(2),repeat=4))
original_bonds=[(site,d) for site in sites for d in range(4)]
original_plaquettes=[(s,mu,nu) for s in sites for mu in range(4) for nu in range(mu+1,4)]
coarse_bonds=[(c,d) for c in coarse_sites for d in range(4)]
selected=[b for c,d in coarse_bonds for b in pair(c,d)]
spectators=set(original_bonds)-set(selected)
assert (len(sites),len(original_bonds),len(original_plaquettes))==(256,1024,1536)
assert (len(coarse_bonds),len(selected),len(set(selected)),len(spectators))==(64,128,128,896)
assert set(selected).isdisjoint(spectators)

midpoints=defaultdict(set)
for c,d in coarse_bonds:
    m=pair(c,d)[1][0]
    midpoints[sign9(m)].add(m)
assert len(midpoints)==32
assert all(len(s)==2 for s in midpoints.values())
assert all({gauge(m) for m in s}=={1,2} for s in midpoints.values())
assert len({sign9(s) for s in sites})==81
# ZERO STRATA: each original C4 coordinate in {1,3} becomes signed zero,
# adding an independent original 1-bit branch. On the whole original
# 4-torus, a projected vertex with r signed zeros has exactly 2**r
# source sites. These are NOT gauge-identifiable.
signed_fibres=defaultdict(set)
for site in sites:
    signed_fibres[sign9(site)].add(site)
strata={r:0 for r in range(5)}
for signed,originals in signed_fibres.items():
    r=sum(x==0 for x in signed[:4])
    assert len(originals)==2**r
    strata[r]+=1
assert strata=={0:16,1:32,2:24,3:8,4:1}
assert sum(strata[r]*2**r for r in strata)==256
# Every lifted original source vertex, edge and Wilson plaquette is lossless.
assert len({lifted_vertex(s) for s in sites})==256
lifted={lifted_bond(b):field_value(b) for b in original_bonds}
assert len(lifted)==1024
assert all(lifted[lifted_bond(b)]==field_value(b) for b in original_bonds)
assert all(lifted_bond(b)[0][1]==b[0] and lifted_bond(b)[1][1]==step(*b)
           for b in original_bonds)

field={b:field_value(b) for b in original_bonds}
transformed=transform(field,gauge)
lifted_transformed={lifted_bond(b):transformed[b] for b in original_bonds}
assert len(lifted_transformed)==1024
for b in original_bonds:
    src,tar,_,_ = lifted_bond(b)
    assert lifted_transformed[lifted_bond(b)]==mul(
        mul(gauge(src[1]), lifted[lifted_bond(b)]),inv(gauge(tar[1])))

# All physical original Wilson plaquette group words survive the lift,
# their gauge conjugation, and therefore their normalized real traces.
trace=lambda q: (1 if q==0 else -1 if q==4 else 0)
original_wilson_sum=0
transformed_wilson_sum=0
for site,mu,nu in original_plaquettes:
    word=plaquette(site,mu,nu)
    p=word_value(word,field)
    lifted_p=word_value(word,{b:lifted[lifted_bond(b)] for b in [(s,d) for s,d,_ in word]})
    gp=word_value(word,transformed)
    lifted_gp=word_value(word,{b:lifted_transformed[lifted_bond(b)] for b in [(s,d) for s,d,_ in word]})
    assert p==lifted_p and gp==lifted_gp
    assert gp==mul(mul(gauge(site),p),inv(gauge(site)))
    assert trace(gp)==trace(p)
    original_wilson_sum+=trace(p)
    transformed_wilson_sum+=trace(gp)
assert original_wilson_sum==transformed_wilson_sum

# Native R445/F19 W=U0*V, V=U1, U0=W*V^-1,
# with odd midpoint h_m NOT identified by its ternary projection.
for c,d in coarse_bonds:
    b0,b1=pair(c,d)
    u,v=field[b0],field[b1]
    assert mul(u,v)!=mul(v,u)
    w=mul(u,v)
    assert mul(w,inv(v))==u
    gu,gv=transformed[b0],transformed[b1]
    gw=mul(gu,gv)
    base=coarse_base(c);target=step(base,d,2)
    assert gw==mul(mul(gauge(base),w),inv(gauge(target)))
    assert mul(gw,inv(gv))==gu

# The Haar reference stays the ORIGINAL 1024-factor Q8 product measure.
# Each F19 map is a bijection of Q8 x Q8; independently applying it to
# 64 disjoint pairs and leaving 896 spectator factors unchanged preserves
# the finite uniform product measure. NOT continuous SU(N) Haar/CMP119 T.
for u,v in product(range(8),repeat=2):
    w=mul(u,v)
    assert mul(w,inv(v))==u
assert len({(mul(u,v),v) for u,v in product(range(8),repeat=2)})==64

print('PASS: 256 actual original sites -> 81 signed-nine projected sites; 256 lifted vertices')
print('PASS: exact source zero-stratum multiplicities {0:16, 1:32, 2:24, 3:8, 4:1}, branch sizes 2**r')
print('PASS: 32 signed zero midpoints, each with 2 independent original gauge-site branches')
print('PASS: all 1024 original Wilson positive bonds, 128 R445 selected, 896 spectators')
print('PASS: 1024/1024 lifted link values and gauge transformation identities')
print('PASS: 1536/1536 original oriented plaquette words, gauge conjugations and real traces')
print('PASS: 64/64 ordered noncommutative native R445/F19 blocks with midpoint cancellation')
print('PASS: each Q8xQ8 F19 map bijective; 64 pairs plus 896 spectator product factor labels retained')
print(f'Full original Wilson trace sum = {original_wilson_sum} (exact, identical after gauge and lift)')
print('LIMIT: exact finite Q8 subgroup source geometry, not continuous Haar, CMP119/122 localized T or OS mass gap')
