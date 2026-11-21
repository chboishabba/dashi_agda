#!/usr/bin/env python3
"""Source-equivalent finite regression of DASHI native ternary geometry weld.

Models the selected Boolean all-neighbour tissue *fixture*, not a measured
PNP or electromagnetic continuum law. Geometry and update rules checked
against existing master Agda owners. Exact symbolic algebra, no CI.
"""
from itertools import product
from sympy import Matrix, Rational as Q

checks = 0

def check(name, cond):
    global checks
    assert bool(cond), name
    checks += 1
    print(f'PASS {checks:02d}: {name}')

TRITS = (-1, 0, 1)
POINTS = tuple(product(TRITS, repeat=3))
IX = {p: i for i,p in enumerate(POINTS)}
segments = ((-1,0), (0,1))
# The exact three families and order of BiologicalFullCubeIncidenceExact.
BONDS = []
for lo,hi in segments:
    for y,z in product(TRITS, repeat=2):
        BONDS.append(((lo,y,z),(hi,y,z)))
for lo,hi in segments:
    for x,z in product(TRITS, repeat=2):
        BONDS.append(((x,lo,z),(x,hi,z)))
for lo,hi in segments:
    for x,y in product(TRITS, repeat=2):
        BONDS.append(((x,y,lo),(x,y,hi)))
BIDX = {b:i for i,b in enumerate(BONDS)}
# Each square boundary: lower-first, upper-second, minus upper-first/lower-second.
SQUARES = []
for (xa,xb),(ya,yb) in product(segments, repeat=2):
    for z in TRITS:
        SQUARES.append((((xa,ya,z),(xb,ya,z)),((xb,ya,z),(xb,yb,z)),
                        ((xa,yb,z),(xb,yb,z)),((xa,ya,z),(xa,yb,z))))
for (xa,xb),(za,zb) in product(segments, repeat=2):
    for y in TRITS:
        SQUARES.append((((xa,y,za),(xb,y,za)),((xb,y,za),(xb,y,zb)),
                        ((xa,y,zb),(xb,y,zb)),((xa,y,za),(xa,y,zb))))
for (ya,yb),(za,zb) in product(segments, repeat=2):
    for x in TRITS:
        SQUARES.append((((x,ya,za),(x,yb,za)),((x,yb,za),(x,yb,zb)),
                        ((x,ya,zb),(x,yb,zb)),((x,ya,za),(x,ya,zb))))

check('exact 27 ternary sites', len(POINTS)==27 and len(set(POINTS))==27)
check('exact 54 native oriented bonds', len(BONDS)==54 and len(set(BONDS))==54)
check('every bond is oriented adjacent, nonperiodic', all(sum(abs(a-b) for a,b in zip(u,v))==1 for u,v in BONDS))
check('exact 36 original elementary squares',len(SQUARES)==36 and len(set(SQUARES))==36)
check('every square has real existing 4 bonds',all(all(edge in BIDX for edge in sq) for sq in SQUARES))
check('every square two-hop endpoint commutes',all(sq[0][0]==sq[3][0] and sq[0][1]==sq[1][0] and sq[3][1]==sq[2][0] and sq[1][1]==sq[2][1] for sq in SQUARES))
check('six outer faces, nine points each',all(sum(p[axis]==sign for p in POINTS)==9 for axis in range(3) for sign in (-1,1)))
check('outer corner incidence 3 faces each',all(sum(abs(t)==1 for t in p)==3 for p in POINTS if all(abs(t)==1 for t in p)))

D=Matrix.zeros(27,54)
for j,(u,v) in enumerate(BONDS):
    D[IX[u],j]=-1
    D[IX[v],j]=1
C=Matrix.zeros(54,36)
for j,sq in enumerate(SQUARES):
    for edge,sign in zip(sq,(1,1,-1,-1)):
        C[BIDX[edge],j]=sign
check('signed internal divergence column sums zero',all(sum(D[:,j])==0 for j in range(54)))
check('36 exact oriented square boundary chains close',D*C==Matrix.zeros(27,36))
check('connected original 27/54 incidence has rank 26',D.rank()==26)
check('original 54-bond cycle kernel dimension is 28',54-D.rank()==28)
check('36 plaquette boundaries span the 28-cycle kernel',C.rank()==28)

# (genome, chromatin, memory, junction, environment, morphology) is the
# exact selected BiologicalHistoryFutureQuotientExact per-site state.
def project(s):
    g,c,h,j,e,m=s
    return (g,h,j,e,m)

def response(fine,p):
    g,c,h,j,e,m=fine[p]
    return bool(g and h and j and e and any(fine[v][3] for (u,v) in BONDS if u==p) or
                g and h and j and e and any(fine[u][3] for (u,v) in BONDS if v==p))

def response_coarse(coarse,p):
    g,h,j,e,m=coarse[p]
    return bool(g and h and j and e and any(coarse[v][2] for (u,v) in BONDS if u==p) or
                g and h and j and e and any(coarse[u][2] for (u,v) in BONDS if v==p))

def fine_step(action, fine):
    out={}
    for p,(g,c,h,j,e,m) in fine.items():
        if action=='signal': m=response(fine,p)
        elif action=='wound': m=False
        elif action=='connect': j=True
        elif action=='restoreMemory': h=True
        elif action=='provideEnvironment': e=True
        else: raise ValueError(action)
        out[p]=(g,c,h,j,e,m)
    return out

def coarse_step(action,coarse):
    out={}
    for p,(g,h,j,e,m) in coarse.items():
        if action=='signal':m=response_coarse(coarse,p)
        elif action=='wound':m=False
        elif action=='connect':j=True
        elif action=='restoreMemory':h=True
        elif action=='provideEnvironment':e=True
        else:raise ValueError(action)
        out[p]=(g,h,j,e,m)
    return out

def make_field(seed):
    return {p:tuple(bool(((i+1)*(j+2)+3*seed+j*j)%7<3) for j in range(6)) for i,p in enumerate(POINTS)}

ACTIONS=('signal','wound','connect','restoreMemory','provideEnvironment')
trials=0
for seed in range(27):
    f=make_field(seed)
    c={p:project(f[p]) for p in POINTS}
    actionseq=tuple(ACTIONS[(seed+2*i)%5] for i in range(8))
    for action in actionseq:
        f=fine_step(action,f)
        c=coarse_step(action,c)
        trials+=1
        assert all(project(f[p])==c[p] for p in POINTS)
        assert all((f[u][3],f[v][3])==(c[u][2],c[v][2]) for u,v in BONDS)
        assert all(response(f,p)==response_coarse(c,p) for p in POINTS)
check('all 216 histories commute at all 27 voxels', trials==216)
check('all 216 histories commute at all 54 bond readouts',trials==216)
check('all 216 histories commute on organizing responses',trials==216)
check('selected simultaneous signal reaches fixed point in one step',all(fine_step('signal',fine_step('signal',make_field(i)))==fine_step('signal',make_field(i)) for i in range(27)))
check('chromatin projection is intentionally inert in selected Boolean model', all(project((g,False,h,j,e,m))==project((g,True,h,j,e,m)) for g,h,j,e,m in product((False,True),repeat=5)))
# Actually test retained memory with same initial visible morphology and enough neighbours.
f0={p:(True,False,False,True,True,False) for p in POINTS}
f1={p:(True,False,True,True,True,False) for p in POINTS}
check('equal current phenotype and different memory split future response',all(f0[p][5]==f1[p][5] for p in POINTS) and any(fine_step('signal',f0)[p][5]!=fine_step('signal',f1)[p][5] for p in POINTS))

# This comparison is solely an ID/face-model gate, not Maxwell physics.
check('native source/target IDs map injectively to all 54 selected directed pairs',len({(IX[u],IX[v]) for u,v in BONDS})==54)
check('reversing one oriented ID pair fails the original positive-bond match',all((IX[v],IX[u]) not in {(IX[a],IX[b]) for a,b in BONDS} for u,v in BONDS))

# Purely source-separated signed finite transport, not unknown PNP chemistry.
J=Matrix([Q(((13*i+7)%11)-5, 3) for i in range(54)])
check('arbitrary rational native internal flux globally sums to zero',sum(D*J)==0)
print(f'{checks}/{checks} exact geometry/Boolean regression checks PASS (SymPy 1.14)')
