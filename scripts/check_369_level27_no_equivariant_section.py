#!/usr/bin/env python3
"""Finite exhaustive non-descent at principal levels 3 and 27.

M=(T^-1 U)^3. M^4=I+9 B with B=[[8336,-5152],[-5152,3184]]
and det(B)≡1 mod3. Hence M^4 fixes exactly those points of
(Z/27)^2 divisible by 3 in both coordinates: 81 points.
Every nonzero vector in (Z/3)^2 is fixed by M^4 but NONE of
its 27-lifts is fixed by M^4. Therefore there is no M-equivariant
section of (Z/27)^2 -> (Z/3)^2 over the nonzero eight-point subset.
This is about finite modular level actions, not the topology of
an analytic punctured plane or an actual VOA state space.
"""
N=27
M=((13,-8),(-8,5)); I=((1,0),(0,1))
def mul(A,B):
 return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2))
                    for j in range(2)) for i in range(2))
X=I
for _ in range(4):X=mul(X,M)
B=tuple(tuple((X[i][j]-I[i][j])//9 for j in range(2)) for i in range(2))
assert B==((8336,-5152),(-5152,3184))
assert (B[0][0]*B[1][1]-B[0][1]*B[1][0])%3==1

def action(A,p,n):
 return tuple(sum(A[i][j]*p[j] for j in range(2))%n for i in range(2))

fixed={p for x in range(N) for y in range(N)
       if (p:=(x,y)) and action(X,p,N)==p}
three_multiple={(x,y) for x in range(N) for y in range(N)
                if x%3==0 and y%3==0}
assert fixed==three_multiple
assert len(fixed)==81

punctured={(x,y) for x in range(3) for y in range(3) if (x,y)!=(0,0)}
for p in punctured:
  lifts=[(x,y) for x in range(N) for y in range(N)
         if (x%3,y%3)==p]
  assert len(lifts)==81
  assert not any(action(X,z,N)==z for z in lifts)
  assert action(X,p,3)==p
print('PASS M^4-I=9B and B invertible modulo 3')
print('PASS exactly 81 fixed level-27 points, all reducing to level-3 zero')
print('PASS all 8 nonzero level-3 points have 81 lifts with NO M^4-fixed lift')
print('THEOREM no M-equivariant section over punctured F3^2 from level 3 to level 27')
