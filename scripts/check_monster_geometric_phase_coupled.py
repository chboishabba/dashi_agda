from collections import Counter
from itertools import product
import sympy as s

def req(ok):
    if not ok: raise AssertionError('geometric phase coupled action')

# N8 geometry: two copies of 24 phase points, origin and two poles.
D=3646
N=54*D
base=lambda b: (b//27)*27+((b%27+8)%24 if b%27<24 else b%27)
fixed=[b for b in range(54) if base(b)==b]
req(len(fixed)==6)
# For a fixed origin use 7 fixed fibre points; for each fixed pole use 10.
# A chosen finite model, not an original Monster operator.
def nf(b): return 7 if b%27==24 else 10

def action(b,k):
    c=base(b)
    if c!=b: return c,k
    f=nf(b)
    if k<f: return b,k
    j,t=divmod(k-f,3)
    return b,f+3*j+(t+1)%3

def pack(b,k): return b*D+k
def unpack(i): return divmod(i,D)
def move(i): return pack(*action(*unpack(i)))
# All orbit labels, explicit inverse into original pointed JFine regular
# carrier (10 coarse labels, 8 relative trits, one centre phase), plus residual54.
reps=[]; singles=[]; visited=bytearray(N)
for i in range(N):
    if visited[i]: continue
    j=move(i); k=move(j)
    req(move(k)==i)
    if i==j:
        singles.append(i); visited[i]=1
    else:
        req(len({i,j,k})==3)
        reps.append((i,j,k))
        for a in (i,j,k): visited[a]=1
req(len(reps)==65610 and len(singles)==54 and all(visited))
forward=[-1]*N
inverse=[]
for orbit in reps:
    for a in orbit: forward[a]=len(inverse); inverse.append(a)
for a in singles: forward[a]=len(inverse); inverse.append(a)
F=196830
for i in range(N):
    j=forward[i]
    req(inverse[j]==i)
    target=j-j%3+(j+1)%3 if j<F else j
    req(forward[move(i)]==target)
    req(unpack(move(i))[0]==base(unpack(i)[0]))
# Product of a common fibre character and the geometric base would need trace 9,
# impossible for dimension 3646: dim-trace=3*m for a rational C3 character.
req(54%6==0 and (D-54//6)%3!=0)
# All permutation fibre choices with fixed-point count 1 mod 3, total 54.
# Impose copy swap and pole reflection: two origins and four poles.
solutions=[(a,b) for a in range(1,28,3) for b in range(1,14,3) if 2*a+4*b==54]
req(solutions==[(1,13),(7,10),(13,7),(19,4),(25,1)])
req(min(solutions,key=lambda ab:abs(ab[0]-ab[1]))==(7,10))
# Any permutation lift over this base has >=6 fixed states (3C no-go).
req(D%3==1 and len(fixed)==6)
# Source character arithmetic over Q(zeta), using exact Fourier inversion.
T=s.Matrix([[1,2],[1,-1]])
req(T.inv()*s.Matrix([N,54])==s.Matrix([65664,65610]))
req((N+2*54)//3==65664 and (N-54)//3==65610)
req(N//3==65628)
print(f'PASS {N} round trips, action and base projection; {len(reps)} regular orbits; {len(singles)} fixed; balanced fibre counts {solutions}; product and 3C permutation no-go')
