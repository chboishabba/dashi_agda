#!/usr/bin/env python3
"""Exact finite YM SU(2) native-plaquette / NONCONSTANT linear-wave seam.

A witness for the 4D periodic Wilson small-field Cartan Hessian and its
one-axis transverse second-difference wave; NOT nonlinear Yang--Mills,
continuous SU(N) Haar, an OS generator, or a positive physical mass gap.
Uses the original 4D six-plane Wilson bond/plaquette orientation.
"""
from itertools import combinations, product
import sympy as s

I, pi = s.I, s.pi

# Matrix Fourier symbol derived from the six native 4D plaquette curls.
# For an SU(2) Cartan direction T=i sigma_3, normalized Wilson trace
# is 1-cos(epsilon F); its Hessian at epsilon=0 is F**2.
for length in (4, 8, 16):
    z = s.cos(2*pi/length) + I*s.sin(2*pi/length)
    d = s.Matrix([0, z-1, 0, 0])  # nonzero momentum along spatial x
    lam = s.simplify(sum(s.conjugate(v)*v for v in d))
    h = (lam*s.eye(4)-d*d.conjugate().T).applyfunc(s.simplify)
    assert h == s.diag(lam, 0, lam, lam)
    assert (h*d).applyfunc(s.simplify) == s.zeros(4, 1)
    # Exact nonzero transverse Fourier mode and gauge zero mode.
    transverse = s.Matrix([0, 0, 1, 0])
    assert (h*transverse-lam*transverse).applyfunc(s.simplify) == s.zeros(4, 1)
    assert s.simplify(lam-(2-z-1/z)) == 0
    assert s.N(lam, 30) > 0
    # Exact traveling wave A_y(x,t)=cos(2*pi*(x-t)/L), satisfying
    # discrete time second difference = discrete spatial x difference.
    for x, t in product(range(length), repeat=2):
        wave = lambda xx, tt: s.cos(2*pi*(xx-tt)/length)
        residual = (wave(x, t+1)-2*wave(x,t)+wave(x,t-1)
                    -wave(x+1,t)+2*wave(x,t)-wave(x-1,t))
        assert s.simplify(s.expand_trig(residual)) == 0
    print(f"L={length}: rank(H)=3, gauge null=1, nonconstant wave exact; "
          f"lambda={lam}")

# Q8 is an actual noncommutative subgroup of SU(2); this checks the
# ORIGINAL full 1024 oriented link labels and all 1536 plaquette words,
# NOT a substitute Haar measure or small-field real analysis.
product_table = {(1,2):(1,3), (2,3):(1,1), (3,1):(1,2),
                 (2,1):(-1,3), (3,2):(-1,1), (1,3):(-1,2)}
def mul(a,b):
    sa,ba=a; sb,bb=b
    if ba==0: return sa*sb,bb
    if bb==0: return sa*sb,ba
    if ba==bb: return -sa*sb,0
    sign,basis=product_table[(ba,bb)]
    return sa*sb*sign,basis

def inv(a):
    sign,basis=a
    return a if basis==0 else (-sign,basis)

def tr(a):
    return 2*a[0] if a[1]==0 else 0

length=4
sites=list(product(range(length),repeat=4))
identity=(1,0)
def step(x,axis):
    y=list(x); y[axis]=(y[axis]+1)%length
    return tuple(y)

# Distinct y-z marked SU(2) Cartan background on the very same
# 4D periodic native bond/plaquette carrier as the original Wilson source.
def background(x,axis):
    if axis==3 and x[2]==1 and x[3]==0: return (1,1)
    if axis==3 and x[2]==1 and x[3]==2: return (-1,0)
    return identity

bond_labels=[(x,axis) for x in sites for axis in range(4)]
assert len(bond_labels)==len(set(bond_labels))==1024
field={bond:background(*bond) for bond in bond_labels}
gauge={x:((1 if (sum(x)+x[0])%2==0 else -1),
          (x[0]+2*x[1]+3*x[2]+x[3])%4) for x in sites}
changed={(x,a):mul(mul(inv(gauge[x]),field[x,a]),gauge[step(x,a)])
         for x,a in bond_labels}

def plaquette(links,x,a,b):
    return mul(mul(mul(links[x,a],links[step(x,a),b]),
                   inv(links[step(x,b),a])),inv(links[x,b]))

plaquette_count=0
wilson_deficit=0
for x in sites:
    for a,b in combinations(range(4),2):
        p=plaquette(field,x,a,b)
        transformed=plaquette(changed,x,a,b)
        assert transformed==mul(mul(inv(gauge[x]),p),gauge[x])
        assert tr(p)==tr(transformed)
        wilson_deficit += 1-s.Rational(tr(p),2)
        plaquette_count+=1
assert plaquette_count==1536
assert wilson_deficit>0

# Distinct original global F/G plaquette marks, NOT marks applied once
# per polymer or a fiction of independent spectator variables.
F=1-s.Rational(tr(plaquette(field,(0,0,0,0),2,3)),2)
G=1-s.Rational(tr(plaquette(field,(0,0,0,2),2,3)),2)
assert (F,G)==(1,2)
ss,tt,bb=s.symbols('s t beta')
marked=(1+ss*F)*(1+tt*G)*s.exp(-bb*wilson_deficit)
coefs=[s.expand(marked).coeff(ss,i).coeff(tt,j) for i,j in
       ((0,0),(1,0),(0,1),(1,1))]
assert coefs==[s.exp(-bb*wilson_deficit)*q for q in (1,F,G,F*G)]
assert s.expand(marked-sum(coefs[k]*term for k,term in enumerate(
       (1,ss,tt,ss*tt))))==0

# Scaling of the transverse Hessian symbol in physical units a=1/L.
scaled=[(n,s.N(4*n*n*s.sin(pi/n)**2,25)) for n in (4,8,16,32)]
assert all(scaled[j][1]<scaled[j+1][1]<s.N(4*pi*pi,25)
           for j in range(len(scaled)-1))
print(f"full original 4D SU(2) subgroup labels={len(bond_labels)}, "
      f"plaquettes={plaquette_count}, original Wilson deficit={wilson_deficit}")
print(f"gauge-invariant distinct original global F,G={F},{G}; "
      "1/F/G/FG coefficients exact")
print("scaled nonzero transverse eigenvalues:",scaled)
print("PASS: finite SU(2) plaquettes + linearized nonconstant wave; "
      "NO nonlinear/OS/continuum mass-gap promotion")
