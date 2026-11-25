"""Exact controls for a norm family, helical projector and split spin summand."""
from itertools import product, permutations
from fractions import Fraction as Q
import sympy as S


def need(b):
    if not b:
        raise ArithmeticError('control failed')

x,t=S.symbols('x t')
h=x*x+t*x-t*t/2
A=2-t**3; B=t**4/4+4*t-2
need(S.expand(h*h-(x**3+A*x+B)-(x**3-2)*(x+2*t-1))==0)
need(S.expand(h.subs(x,1-2*t)-(1-3*t+3*t*t/2))==0)
counts=[]
for p in (5,7):
    a,b=-6,10
    need((-16*(4*a**3+27*b*b))%p!=0)
    pts=[None]+[(i,j) for i,j in product(range(p),repeat=2) if (j*j-i**3-a*i-b)%p==0]
    def add(P,R):
        if P is None:return R
        if R is None:return P
        i,j=P;k,l=R
        if i==k and (j+l)%p==0:return None
        m=((l-j)*pow(k-i,-1,p) if i!=k else (3*i*i+a)*pow(2*j,-1,p))%p
        z=(m*m-i-k)%p
        return z,(m*(i-z)-j)%p
    P=(-3%p,-1%p);R=None
    need(P in pts)
    for n in range(1,len(pts)+1):
        R=add(R,P)
        if R is None:break
    counts.append((len(pts),n))
    if p==7:need(P not in {add(add(R,R),R) for R in pts})
need(counts==[(8,4),(6,6)])
for k in range(-20,21):
    u=2+70*k
    need((2-u**3+6)%35==0 and (u**4//4+4*u-12)%35==0)
    need((1-2*u+3)%35==0 and (1-3*u+3*u*u//2-1)%35==0)
print('BSD norm family, two exact reduction orders, 41 congruence controls')

# Actual transverse helical projector on rational unit directions.
ks=[S.Matrix([Q(2*a,1+a*a+b*b),Q(2*b,1+a*a+b*b),Q(1-a*a-b*b,1+a*a+b*b)]) for a,b in product(range(-3,4),repeat=2)]
for k in ks:
    C=S.Matrix([[0,-k[2],k[1]],[k[2],0,-k[0]],[-k[1],k[0],0]])
    P=S.eye(3)-k*k.T
    J=S.I*C
    plus=(P+J)/2; minus=(P-J)/2
    simp=lambda M:M.applyfunc(S.expand)
    need(k.dot(k)==1 and simp(plus*plus-plus)==S.zeros(3))
    need(simp(minus*minus-minus)==S.zeros(3) and simp(plus*minus)==S.zeros(3))
    need(simp(J*plus-plus)==S.zeros(3) and simp(J*minus+minus)==S.zeros(3))
    need(simp(plus.conjugate()-minus)==S.zeros(3) and k.T*plus==S.zeros(1,3))
print('NS 49 exact transverse helical projectors')

# Fock model of the split rank18 Clifford algebra over K: 9 hyperbolic pairs.
# gamma_{2j}=creation+contraction, gamma_{2j+1}=creation-contraction.
def gamma(i,m):
    j=i//2
    sign=(-1)**((m&((1<<j)-1)).bit_count())
    if i%2 and m&(1<<j):sign=-sign
    return sign,m^(1<<j)
def word(seq,m):
    s=1
    for i in reversed(seq):
        a,m=gamma(i,m);s*=a
    return s,m
sectors={p:[] for p in product(range(2),repeat=3)}
for m in range(512):
    p=tuple(((m>>(3*j))&7).bit_count()%2 for j in range(3))
    sectors[p].append(m)
    for j in range(3):need(word(range(6*j,6*j+6),m)==((-1)**p[j],m))
need(all(len(v)==64 for v in sectors.values()))
for m in range(512):
    for i in range(18):
        need(word((i,i),m)==((-1)**(i%2),m))
for p,states in sectors.items():
    for j in range(3):
        # The alternating sum of three disjoint bivectors on a single sector.
        total=0
        for seq in permutations(range(6*j,6*j+6)):
            sign=(-1)**sum(seq[a]>seq[b] for a in range(6) for b in range(a+1,6))
            # Clifford anticommutation proves the same coefficient for every state;
            # verify the first, then use all-state volume checks above.
            s,m=word(seq,states[0]);need(m==states[0] and s==sign*(-1)**p[j])
            total+=sign*s*len(states)
        need(total==720*64*(-1)**p[j])
print('Hodge 8 sectors of rank64; 512 volume checks per block; 17280 ordered sector traces')
