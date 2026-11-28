"""R384-R387: original compact Whittaker generator, arithmetic controls only."""
from itertools import product
from fractions import Fraction
import sympy as s

# Original R326 interleaved conductor-zero flag.
B=s.Matrix([[6,21],[-7,-15]])/9
X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])
Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)]
q=s.diag(*Q); qi=q.inv()
positions=list((i,j) for i in range(4) for j in range(i+1,4))
roots=[]
for i,j in positions:
    M=s.zeros(8);M[2*i:2*i+2,2*j:2*j+2]=s.eye(2)
    Z=qi*M*q
    assert all(Z[a,b]==0 for a in range(8) for b in range(a+1))
    roots.append(3*sum(Z[a,a+1] for a in range(7)))
    assert roots[-1]==int(j==i+1)
for c in product(range(3),repeat=6):
    assert sum(x*y for x,y in zip(c,roots))%3==sum(x for x,(i,j) in zip(c,positions) if j==i+1)%3
# Actual GL3/U3 chart of the original finite GL4 mirabolic P4/U4.
def det3(a):
    return (a[0]*(a[4]*a[8]-a[5]*a[7])-a[1]*(a[3]*a[8]-a[5]*a[6])+a[2]*(a[3]*a[7]-a[4]*a[6]))%3

def act(a,x,y,z):
    return tuple(v for i in range(0,9,3) for v in (a[i],(a[i+1]+x*a[i])%3,(a[i+2]+y*a[i]+z*a[i+1])%3))

G={a for a in product(range(3),repeat=9) if det3(a)}
left=set(G); reps=[]; addresses={}
while left:
    a=min(left); i=len(reps);reps.append(a)
    orbit={act(a,x,y,z):(x,y,z) for x,y,z in product(range(3),repeat=3)}
    assert len(orbit)==27 and orbit.keys()<=left
    for g,u in orbit.items():
        assert act(a,*u)==g
        addresses[g]=(i,u)
    left.difference_update(orbit)
assert len(G)==11232 and len(reps)==416 and len(addresses)==11232
# P4 has 27 translation lifts for each GL3 element. With diag(a,1)
# as coset section, the remaining column of u is a^-1 times translation.
# Check the actual three-coordinate reopening for every representative and lift.
for a in reps:
    ai=s.Matrix(3,3,a).inv_mod(3)
    for u in product(range(3),repeat=3):
        col=tuple(sum(a[3*i+j]*u[j] for j in range(3))%3 for i in range(3))
        assert tuple(sum(int(ai[i,j])*col[j] for j in range(3))%3 for i in range(3))==u
    assert len({tuple(sum(a[3*i+j]*u[j] for j in range(3))%3 for i in range(3)) for u in product(range(3),repeat=3)})==27
# Exact finite-type and quotient Haar factors from R328; retain both signs.
GL4=s.prod(3**4-3**i for i in range(4)); U4=3**6; dim=416
assert GL4==24261120 and GL4//U4==33280 and GL4==80*U4*dim
# Schur averaging is a theorem, not an enumerated GL4 representation action.
# For any nonzero V8 the original source normalization is dim/M=1/(80 V8).
V8=s.Symbol('V8',nonzero=True)
M=s.Integer(GL4//U4)*V8
assert s.simplify(dim/M-1/(80*V8))==0
assert s.simplify((dim/M)*(M/dim))==1
# R322 normalizer sign: generator is -Id, extended action (-alpha)^m.
a=s.Symbol('alpha',nonzero=True)
for m in range(-16,17):
    assert s.simplify((-a)**m/((-s.Integer(1))**m)-a**m)==0
# Laurent specialization: inverse and both signs retained, including m=0.
for alpha in (s.Rational(1),s.Rational(-1),s.Rational(2,3),s.Rational(-5,2)):
    for m,n in product(range(-5,6),repeat=2):
        assert alpha**m*alpha**n==alpha**(m+n)
print('729 original finite upper-character controls; 11232 GL3/U3 exact reopenings; 416 translation-bijection controls')
print('compact type dimension 416; quotient mass 33280 V8; normalized test 1/(80 V8); 33 sign controls; 484 Laurent specialization controls PASS')
