#!/usr/bin/env python3
"""Original 4D Wilson/F19 W0: exact Q8 fine-mark/coarse-block counterexample.
Q8 is an SU(2) subgroup for finite algebra; no continuous Haar or RG claim.
Two original disjoint y-z plaquettes at (0,0,0,0), (0,0,0,2).
"""
from itertools import product, combinations
from sympy import symbols, expand, exp

mul_basis = {(1,2):(1,3), (2,3):(1,1), (3,1):(1,2),
             (2,1):(-1,3), (3,2):(-1,1), (1,3):(-1,2)}
def mul(a,b):
    sa,ba=a; sb,bb=b
    if ba==0: return (sa*sb,bb)
    if bb==0: return (sa*sb,ba)
    if ba==bb: return (-sa*sb,0)
    sign,basis=mul_basis[ba,bb]
    return sa*sb*sign,basis
def inverse(a):
    return a if a[1]==0 else (-a[0],a[1])
def trace(a):
    return 2*a[0] if a[1]==0 else 0
def step(site,axis):
    next_site=list(site); next_site[axis]=(next_site[axis]+1)%4
    return tuple(next_site)
identity=(1,0)
i=(1,1)
minus_i=(-1,1)
fine_sites=list(product(range(4),repeat=4))
coarse_sites=list(product(range(2),repeat=4))
fine_bonds=[(x,axis) for x in fine_sites for axis in range(4)]
coarse_bonds=[(x,axis) for x in coarse_sites for axis in range(4)]
assert len(fine_bonds)==len(set(fine_bonds))==1024
assert len(coarse_bonds)==64

def plaquette(field,site,a,b):
    return mul(mul(mul(field[site,a],field[step(site,a),b]),
                   inverse(field[step(site,b),a])),
               inverse(field[site,b]))
def block(field,coarse,axis):
    origin=tuple(2*x for x in coarse)
    return mul(field[origin,axis], field[step(origin,axis),axis])
F_site=(0,0,0,0); G_site=(0,0,0,2)
def build(fchanged,gchanged):
    field={bond:identity for bond in fine_bonds}
    for site,enabled in ((F_site,fchanged),(G_site,gchanged)):
        if enabled:
            # Both links lie in the SAME selected native axial block.
            field[site,2]=i
            field[step(site,2),2]=minus_i
    return field

rows=[]
for fchanged,gchanged in product((0,1),repeat=2):
    field=build(fchanged,gchanged)
    blocks=[block(field,site,axis) for site,axis in coarse_bonds]
    assert all(w==identity for w in blocks)
    F=1-trace(plaquette(field,F_site,2,3))//2
    G=1-trace(plaquette(field,G_site,2,3))//2
    deficit=sum(1-trace(plaquette(field,site,a,b))//2
                for site in fine_sites for a,b in combinations(range(4),2))
    assert (F,G,deficit)==(fchanged,gchanged,12*(fchanged+gchanged))
    rows.append((F,G,deficit,tuple(blocks)))
assert all(row[3]==rows[0][3] for row in rows)
assert {(row[0],row[1]) for row in rows}==set(product((0,1),repeat=2))

# Conditional fibre correlations are not determined by W alone. A
# weighted positive four-point conditional law may be dependent even
# though all four assignments have the same 64 coarse links.
s,t,beta,kappa=symbols("s t beta kappa", positive=True)
# In this restricted quartet the Wilson weights factor, so we do NOT
# incorrectly claim a nonzero fibre covariance in this particular test.
Z=sum(exp(-beta*D)*(1+s*F)*(1+t*G) for F,G,D,_ in rows)
expected=(1+exp(-12*beta)*(1+s))*(1+exp(-12*beta)*(1+t))
assert expand(Z-expected)==0
# Nonetheless a coarse-only mark predicts the same F for each row,
# which is contradicted by the two rows with F=0 and F=1.
assert rows[0][3]==rows[2][3] and rows[0][0]!=rows[2][0]
assert rows[0][3]==rows[1][3] and rows[0][1]!=rows[1][1]
print("PASS: 1024 fine links, 64 identical coarse R445 holonomies, "
      "4 independent fine F/G states, Wilson deficits [0,12,12,24]")
print("PASS: strict fine-mark nonfactorability through coarse W; "
      "restricted quartet fibre covariance remains zero")
print("NO continuous Haar, no full F19 measure, no CMP119 density, no W3")
