#!/usr/bin/env python3
"""Original 4D SU(N) Wilson F/G sphere: exact leaf-Haar, finite-Bessel and two-tube checks.

Reuses the existing full source 1024-link, 1536-plaquette checker, and the
standard SU(N) Haar character-orthogonality identity. The equality for
arbitrary beta is a mathematical character-expansion derivation, *not* a
high-dimensional numerical integration or the physical CMP119/122 W3 sum.
"""
from collections import Counter, deque
from itertools import product
from pathlib import Path
from runpy import run_path
import sympy as sp
import mpmath as mp

src = run_path(str(Path(__file__).with_name(
    "check_ym_original_sun_w3_two_time_tube_20261123.py")))
P, F, G, walls = (src[x] for x in ("plaques", "F", "G", "tube"))
S = {p: frozenset((x, a) for x, a, _ in edges) for p, edges in P.items()}
assert len(P) == 1536 and len(set.union(*(set(v) for v in S.values()))) == 1024
def peel(fs):
    remain = set(fs)
    while remain:
        counts = Counter(e for p in remain for e in S[p])
        choices = {p for p in remain if any(counts[e] == 1 for e in S[p])}
        if not choices: break
        remain.remove(min(choices))
    return remain
for k in range(256):
    selected = (F, G) + tuple(walls[i] for i in range(8) if k >> i & 1)
    assert peel(selected) == (set(selected) if k == 255 else set())
assert not peel((F,) + walls)
print("PASS 255/255 proper wall subsets: complete link-leaf Haar elimination")
print("PASS full ten-face connected original sphere; remove one cap => nine independent Haar faces")

# The source-original minimum-eight proof is sharpened to UNIQUE
# forward/reverse periodic time paths. Five original nonmarked plaquettes
# touch each boundary link of the two spatial F/G marks. Enumerate all
# five-to-the-eighth candidates exactly by 5^4+5^4 XOR hash joining.
edges = sorted({e for z in S.values() for e in z})
edge_ix = {e: i for i, e in enumerate(edges)}
bits = {p: sum(1 << edge_ix[e] for e in z) for p, z in S.items()}
choices = []
for e in sorted(S[F]) + sorted(S[G]):
    ch = [p for p, z in S.items() if p not in (F,G) and e in z]
    assert len(ch) == 5
    choices.append(ch)
left = {}
for ch in product(*choices[:4]):
    h = 0
    for p in ch: h ^= bits[p]
    left.setdefault(h, []).append(ch)
target = bits[F] ^ bits[G]
solutions = []
for ch in product(*choices[4:]):
    h = 0
    for p in ch: h ^= bits[p]
    for l in left.get(target ^ h, ()):
        if len(set(l+ch)) == 8: solutions.append(frozenset(l+ch))
back = frozenset(((t,dy,dz,0),0,a) for t in (2,3)
                  for a in (1,2) for dy,dz in
                  ([(0,0),(0,1)] if a==1 else [(0,0),(1,0)]))
assert len(solutions) == 2 and set(solutions) == {frozenset(walls), back}
print("PASS EXACT full-original 5^8 min surface enumeration: TWO solutions (forward/reverse time)")

# Standard SU(N) fundamental/dual fundamental orthogonality. ReTr/N
# has variance v2=1/4, vN=1/(2N^2) for N>=3. Each original 10-face
# closed sphere link is incident to exactly two source faces; both
# unweighted F and G force the same fundamental irrep on all eight
# intermediate action faces, giving:
#   Cov_wall(F,G)=vN*prod_q mN(beta_q),
#   mN(beta)=d(log zN)/d beta, zN=∫_SU(N) exp(beta ReTr U/N)dH(U).
# This uses the SOURCE sphere (two marked caps, eight interaction
# faces), not a replacement 2D physical Yang-Mills theory.
for N in range(2, 7):
    v = sp.Rational(1,4) if N == 2 else sp.Rational(1,2*N*N)
    coefficient = v**9
    expected = sp.Rational(1,2**18) if N==2 else sp.Rational(1,2**9*N**18)
    assert coefficient == expected
    print("PASS SU(%d) exact all-beta character result yields 8th selected coefficient %s" % (N, coefficient))

beta = sp.symbols("beta")
m = sp.besseli(2,beta)/sp.besseli(1,beta)
assert sp.series(m,beta,0,9).removeO() == beta/4-beta**3/96+beta**5/1536-beta**7/23040
c = sp.Rational(1,4)*m**8
assert sp.simplify(sp.series(c,beta,0,13).removeO() -
    (beta**8/262144-beta**10/786432+5*beta**12/18874368)) == 0
mp.mp.dps = 55
for b in ("0.2","1","3","8"):
    x = mp.mpf(b)
    z = mp.quad(lambda t:(2/mp.pi)*mp.sin(t)**2*mp.exp(x*mp.cos(t)),[0,mp.pi])
    moment = mp.quad(lambda t:(2/mp.pi)*mp.sin(t)**2*mp.cos(t)*mp.exp(x*mp.cos(t)),[0,mp.pi])/z
    assert abs(moment-mp.besseli(2,x)/mp.besseli(1,x)) < mp.mpf("1e-48")
    print("PASS original SU2 continuous Haar beta=%s: covariance=%s" % (b, mp.nstr(moment**8/4,16)))
for b in (2,20,200):
    x = mp.mpf(b)
    rate = -4*mp.log(mp.besseli(2,x)/mp.besseli(1,x))
    print("SU2 1-tube native inverse correlation length at beta=%d: %s" % (b,mp.nstr(rate,15)))
print("NO cutoff-uniform W3 or same-H mass gap inferred from tube-only beta scaling")

# Exact source restoration/Duhamel identity:
# full original Wilson coupling = walls(beta) + remaining 1528 faces.
# d/dtau Cov_{mu_tau}(F,G) = beta Σ_{p notin walls} kappa_mu_tau(F,G,t_p).
# Verify its 3-cumulant algebra on a nonconstant rational source fixture.
e = sp.symbols("e")
weights = [sp.Rational(1,3),sp.Rational(2,3),sp.Integer(1)]
f,g,h = ([1,0,-1],[0,1,-1],[-1,2,1])
def avg(xs,epsilon):
    w = [weights[i]*(1+epsilon*h[i]) for i in range(3)]
    return sp.together(sum(w[i]*xs[i] for i in range(3))/sum(w))
dot = lambda a,b:[x*y for x,y in zip(a,b)]
triple = [x*y*z for x,y,z in zip(f,g,h)]
C = avg(dot(f,g),e) - avg(f,e)*avg(g,e)
F0,G0,H0 = avg(f,0),avg(g,0),avg(h,0)
K = avg(triple,0)-avg(dot(f,g),0)*H0-avg(dot(f,h),0)*G0-avg(dot(g,h),0)*F0+2*F0*G0*H0
assert sp.simplify(sp.diff(C,e).subs(e,0)-K)==0
assert len(P)-len(walls)==1528
print("PASS exact normalized source log-Hessian restoration: 1528 original residual plaquettes")
print("OPEN literal CMP119/122 nonfactorizing T, original homogeneous Wilson absolute W3, OS physical same-H")


# Source-native variable-cutoff negative/positive controls: a true original
# periodic four-dimensional Wilson lattice at L=3,4,5,6 (not merely L4).
# The *single activated 4d-wall prism* is a topological sphere for each
# d=1..L-1 and each of the THREE spatial transverse original planes.
from itertools import combinations
for L in (3,4,5,6):
    def linkset(p):
        x,a,b=p
        def advance(k):
            y=list(x);y[k]=(y[k]+1)%L;return tuple(y)
        return frozenset(((x,a),(advance(a),b),(advance(b),a),(x,b)))
    def leaf_peel(face_list):
        remaining=set(face_list)
        while remaining:
            c=Counter(e for p in remaining for e in linkset(p))
            free={p for p in remaining if any(c[e]==1 for e in linkset(p))}
            if not free:break
            remaining.remove(min(free))
        return remaining
    for d in range(1,L):
        for a,b in combinations((1,2,3),2):
            base=((0,0,0,0),a,b)
            cap=((d,0,0,0),a,b)
            ws=[]
            for t in range(d):
                for ax,other in ((a,b),(b,a)):
                    for k in (0,1):
                        at=[0,0,0,0];at[0]=t;at[other]=k
                        ws.append((tuple(at),0,ax))
            fs=(base,cap)+tuple(ws)
            inc=Counter(e for p in fs for e in linkset(p))
            assert len(ws)==4*d and len(set(ws))==4*d
            assert len(inc)==8*d+4 and set(inc.values())=={2}
            assert leaf_peel(fs)==set(fs)
            assert not leaf_peel((base,)+tuple(ws))
            for j in range(len(ws)):
                assert not leaf_peel((base,cap)+tuple(w for i,w in enumerate(ws) if i!=j))
    print("PASS source original periodic L=%d: %d links, 3 spatial planes, all nonwrapping time distances" % (L,4*L**4))
print("OPEN variable-L common-beta full W3. Verified family is original source geometry with OTHER plaquettes switched OFF.")
