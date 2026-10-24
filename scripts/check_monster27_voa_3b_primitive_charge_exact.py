#!/usr/bin/env python3
"""Source-anchored exact Monster V^natural weight-two C27/3B charge audit.
External math premises:
FLM weight2 = trivial 1 + rational irreducible 196883;
Monster 27A/B have order27 and their ninth powers are class3B;
T_3B(q)=12+(eta(tau)/eta(3tau))^12=q^-1+54q-76q²+...
No explicit 196883x196883 matrix, VOA realization, or cube↔VOA
intertwiner is claimed. Monster 27A/27B ordinary characters coincide.
"""
from math import comb,gcd
import sympy as s
N=6
def mul(a,b):
 return [sum(a[k]*b[i-k] for k in range(i+1)) for i in range(N+1)]
eta=[1]+[0]*N
inv=[1]+[0]*N
for n in range(1,N+1):
 f=[0]*(N+1)
 for k in range(min(12,N//n)+1):f[k*n]=(-1)**k*comb(12,k)
 eta=mul(eta,f)
 if 3*n<=N:
  fi=[0]*(N+1)
  for k in range(N//(3*n)+1):fi[3*n*k]=comb(11+k,k)
  inv=mul(inv,fi)
coeff=mul(eta,inv)
assert coeff[:5]==[1,-12,54,-76,-243]
assert coeff[1]+12==0
# Rational Monster irreducible restriction to cyclic C27:
# Q(C27) = products Q(zeta_d) for d=1,3,9,27,
# characters on g^j are the Ramanujan sums.
D=(1,3,9,27); powers=(0,1,3,9)
def ram(d,j):
 h=gcd(d,j)
 return int(s.mobius(d//h)*s.totient(d)//s.totient(d//h))
A=s.Matrix([[ram(d,j) for d in D] for j in powers])
assert A==s.Matrix([[1,2,6,18],[1,-1,0,0],
                     [1,2,-3,0],[1,2,6,-9]])
assert A.det()==-729
chi1,chi3=s.symbols('chi_27 chi_9',integer=True)
mult=s.simplify(A.inv()*s.Matrix([196884,chi1,chi3,54]))
assert mult[3]==7290
assert 18*7290==131220 and 9*7290==65610
assert 65664+2*65610==196884
assert (196883-53)//27==7290
units=[k for k in range(27) if gcd(k,27)==1]
assert len(units)==18 and sum(k%3==1 for k in units)==9
assert sum(k%3==2 for k in units)==9
# Existing DASHI Monster3B finite model: F3^6 × Fin90 = 729 ×90.
# An order27 refined primitive eigenspace is 81 ×90 =7290.
# Exact dimension reconciliation only; basis intertwiner not automatic.
assert 729*90==65610 and 9*81*90==65610
assert 81*90==7290 and 27**3==19683
print('PASS 3B eta Hauptmodul prefix q^-1 +54q -76q² -243q³')
print('PASS C27 rational character inversion and primitive multiplicity=7290 each')
print('PASS actual V2 3B sectors 65664,65610,65610')
print('PASS existing 729x90=65610 model refines numerically into 9x81x90')
print('OPEN natural g-eigenbasis on existing Heisenberg model, C27 twisted trace, cube coupling and AdS3/KK')
