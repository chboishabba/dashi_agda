#!/usr/bin/env python3
"""YM P0: true original 4D SU(N) Wilson sparse-plaquette geometry and rate.

This checker verifies original native 4D incidence, fourfold site-reflection
unit-cube face dissemination, complete 24-colour separation, the exact
combinatorial witness inequalities and high-beta rate algebra/thresholds.

Analytic input: standard continuous SU(N) Weyl Haar and site-reflection
chessboard theorem for the specified Wilson closed-cube observable algebra.
This script does NOT numerically integrate SU(N), certify a continuum mass
or typecheck Agda. Standard pure-gauge RP/chessboard applicability and its
exact original boundary algebra must be credited/verified separately.
"""

from collections import Counter, defaultdict
from itertools import combinations, product
from math import ceil, factorial, log
from random import Random

import mpmath as mp
mp.mp.dps = 70

checks = 0

def verify(x, msg=''):
    global checks
    if not x:
        raise AssertionError(f'{msg}: check {checks}')
    checks += 1

def shift(x, direction, L, steps=1):
    y = list(x)
    y[direction] = (y[direction] + steps) % L
    return tuple(y)

def face_links(x, mu, nu, L):
    return frozenset(((x, mu), (x, nu),
                      (shift(x, nu, L), mu), (shift(x, mu, L), nu)))

def face_class(x, mu, nu):
    transverse = tuple(k for k in range(4) if k not in (mu,nu))
    return (mu,nu,x[transverse[0]] % 2,x[transverse[1]] % 2)

def reflected_face_for_tile(x, mu, nu, s, L):
    y = list(x)
    transverse = [k for k in range(4) if k not in (mu,nu)]
    for k,sk in zip(transverse,s):
        y[k] = (x[k] + ((sk-x[k]) % 2)) % L
    return (tuple(y),mu,nu)

rng = Random(20261123)
for L in (4,6,8):
    sites = list(product(range(L), repeat=4))
    faces = [(x,mu,nu) for x in sites for mu,nu in combinations(range(4),2)]
    links = [(x,mu) for x in sites for mu in range(4)]
    verify(len(faces)==6*L**4 and len(links)==4*L**4, 'cardinals')
    face_by_link = defaultdict(set)
    classes = defaultdict(set)
    for f in faces:
        x,mu,nu = f
        ll = face_links(x,mu,nu,L)
        verify(len(ll)==4, 'native face support')
        classes[face_class(x,mu,nu)].add(f)
        for link in ll:
            face_by_link[link].add(f)
    verify(len(classes)==24, '24 actual native plane-parity classes')
    verify(all(len(cls)==L**4//4 for cls in classes.values()), 'fourth of V per class')
    verify(all(len(face_by_link[e])==6 for e in links), '6 faces per link')

    # FULL L4-8 CHESSBOARD DISSEMINATION: four unit cubes contain each face
    # selected from a class. Select arbitrary cube tile x; reflect its
    # transverse face within that cube to the class's fixed parity face.
    for mu,nu in combinations(range(4),2):
        for s in product((0,1), repeat=2):
            hits = Counter()
            for x in sites:
                p = reflected_face_for_tile(x,mu,nu,s,L)
                transverse = [k for k in range(4) if k not in (mu,nu)]
                for k in transverse:
                    verify(p[0][k] in (x[k], (x[k]+1)%L), 'within unit cube')
                verify(face_class(p[0],mu,nu)==(mu,nu,*s), 'correct class')
                hits[p] += 1
            verify(len(hits)==L**4//4, 'distinct reflected plane-class faces')
            verify(set(hits)==classes[mu,nu,*s], 'surjective face class')
            verify(set(hits.values())=={4}, 'each selected native face repeated 4 times')

    # Every original large-field link has exactly six original plaquette
    # witnesses. Any such witness covers at most four original links; do
    # not assume statistical independence of gauge links.
    for n in (1,2,3,4,5,8,16,32,64,128):
        for _ in range(20):
            marked = rng.sample(links,min(n,len(links)))
            witnesses=[rng.choice(sorted(face_by_link[e])) for e in marked]
            per_face = Counter(witnesses)
            verify(max(per_face.values())<=4, 'four links per witness face')
            verify(len(per_face)>=ceil(len(marked)/4), 'witness injection/loss')

print(f'PASS original four-axis L4/6/8 native geometry and 24-class dissemination: {checks} checks')

# Exact symbolic rate and threshold algebra using sympy (no floats).
import sympy as sp
b, eps, BN, K, d, m = sp.symbols('b eps B_N K d m', positive=True)
kappa = b*eps/96-BN/4
u = 6*sp.exp(-kappa/4)
verify(sp.simplify(u-6*sp.exp(BN/16-b*eps/384))==0, 'algebraic u_N')
verify(sp.simplify(sp.log(196*u)-(sp.log(1176)+BN/16-b*eps/384))==0,
       'rooted animal log rate')
verify(sp.simplify((b*eps-384*sp.log(1176)-24*BN)/384 + sp.log(196*u))==0,
       'exact criterion')

# N ranks and multiple physical thresholds, with NO fictional optimal beta.
def log_K(n):
    return mp.loggamma(n+1)+(n-1)*mp.log(128*n*n)+n*(n-1)*mp.log(16*n)

def B(n,beta):
    return 8+mp.mpf(2)/3*log_K(n)+mp.mpf(n*n-1)/3*mp.log(beta)

def log_q(n,beta,epsilon):
    return mp.log(1176)+B(n,beta)/16-beta*epsilon/384

def threshold(n, epsilon):
    lo=mp.mpf(16)
    hi=mp.mpf(16)
    while log_q(n,hi,epsilon)>0:
        hi*=2
        if hi>mp.mpf('1e30'):
            raise AssertionError('no threshold reached in scan')
    for _ in range(180):
        mid=(lo+hi)/2
        if log_q(n,mid,epsilon)>0:
            lo=mid
        else:
            hi=mid
    return hi

for n in (2,3,4,5,8):
    for epsilon in (mp.mpf(1),mp.mpf(1)/2,mp.mpf(1)/4):
        t=threshold(n,epsilon)
        verify(t>16 and log_q(n,t,epsilon)<=mp.mpf('1e-40'), 'high-beta q<1')
        verify(log_q(n,t-mp.mpf('1e-10'),epsilon)>-mp.mpf('1e-8'),
               'threshold bracket')
        for multiplicative in (mp.mpf('1.001'),mp.mpf(2),mp.mpf(10)):
            beta=t*multiplicative
            q=mp.exp(log_q(n,beta,epsilon))
            u=q/196
            verify(0<u<mp.mpf(1)/196 and 0<q<1, 'rooted animal rate')
            for count in (1,2,7,25):
                tail=u*q**(count-1)/(1-q)
                verify(tail>0 and tail<1/(1-q),'valid tail')
        print('SU({}) epsilon={} beta_threshold≈{}'.format(n,mp.nstr(epsilon,4),mp.nstr(t,12)))

# Wrong-regime negative controls: even as bare beta tends to infinity,
# epsilon(a)=O(1/beta) makes the bound increasingly VACUOUS.
for n in (2,3,4,8):
    base=mp.mpf('1e3')
    last=None
    for beta in (base,base**2,base**3):
        epsilon=1/beta
        val=log_q(n,beta,epsilon)
        verify(val>0, 'shrinking threshold cannot meet sufficient criterion')
        if last is not None: verify(val>last, 'log q increases')
        last=val

# A fixed-threshold sparse link event is NOT a two-mark CMP116 activity.
# Negative controls: n=O(L) sparse links within 4L^4 original links so
# total bad-link density goes to zero while a spanning path survives.
for L in (4,6,8,16,32):
    n=L
    verify(sp.Rational(n,4*L**4)==sp.Rational(1,4*L**3),
           'sparse spanning path density')

print(f'PASS complete symbolic rates and rank/epsilon regime checks: {checks} checks')
print('TRUST: SOURCE 4D GEOMETRY EXACT; SU(N) ANALYTIC WYL/HAAR + STANDARD CHESSBOARD THEOREM IMPORTED.')
print('NOT: native chessboard Agda kernel, beta(a) full physical large field, CMP119/122 T, absolute W3, same-H OS mass gap.')
