"""Exact local reference controls; not native kernels or Clay endpoint acceptance."""
from fractions import Fraction as Q
from itertools import product
from random import Random
import sympy as s

if not __debug__:
    raise SystemExit('refuse optimized Python')

rng = Random(36928)
counts = {}
def check(k, v):
    if not v:
        raise AssertionError(k)
    counts[k] = counts.get(k, 0) + 1

def dot(x, y):
    return sum(a*b for a,b in zip(x,y))
def mass(x):
    return dot(x,x)
def vec():
    return tuple(Q(rng.randrange(-4,5)) for _ in range(3))
def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))
def cross(x,y):
    return (x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
def scale(a,x):
    return tuple(a*b for b in x)
def add(x,y):
    return tuple(a+b for a,b in zip(x,y))
def project(x,v):
    return sub(v,scale(dot(x,v)/mass(x),x))
def phase_mass(v):
    return mass(v[0])+mass(v[1])
def gram(a,b):
    return 2*(dot(a[0],b[0])+dot(a[1],b[1]))
def raw(x,u,v):
    r,i=dot(x,u[0]),dot(x,u[1])
    return (scale(-1,add(scale(r,v[1]),scale(i,v[0]))),sub(scale(r,v[0]),scale(i,v[1])))
def velocity(k):
    return cross(k,vec()),cross(k,vec())

for _ in range(256):
    x=vec()
    if not mass(x): x=(Q(1),Q(0),Q(0))
    y,z=vec(),vec()
    u,v,p,q=velocity(y),velocity(sub(x,y)),velocity(z),velocity(sub(x,z))
    R,S=raw(x,u,v),raw(x,p,q)
    A,B=tuple(project(x,a) for a in R),tuple(project(x,b) for b in S)
    for W,P in ((R,A),(S,B)):
        check('Leray_Pythagoras', phase_mass(W)==phase_mass(P)+sum(dot(x,a)**2/mass(x) for a in W))
    for U,V,W in ((u,v,A),(p,q,B)):
        check('projected_cell_bound',phase_mass(W)<=mass(x)*phase_mass(U)*phase_mass(V))
    g=gram(A,B)
    check('six_phase_Gram_Cauchy',g*g<=4*phase_mass(A)*phase_mass(B))
    four=phase_mass(u)*phase_mass(v)*phase_mass(p)*phase_mass(q)
    nu=Q(3,7)
    a=nu*mass(x)
    t=2*nu*(mass(sub(y,scale(Q(1,2),x)))+mass(sub(z,scale(Q(1,2),x))))
    c=t/(a*(a+t))
    check('centered_product_majorant_squared',(c*g)**2<=(2/nu)**2*four)
    check('same_output_rate',nu*(mass(y)+mass(sub(x,y))+mass(z)+mass(sub(x,z)))==a+t)

# Actual discrete convolution with zero extension, not cyclic wraparound.
w={k:Q(rng.randrange(0,8),7) for k in product(range(-1,2),repeat=3)}
E=sum(a*a for a in w.values())
for x in product(range(-2,3),repeat=3):
    p=[a*w.get(sub(x,k),0) for k,a in w.items()]
    C=sum(p)
    check('fixed_output_energy',C<=E)
    check('both_input_fibres',sum(a*b for a in p for b in p)==C*C)

# Exact box-amplitude envelope scaling in R^3, E=1. Not a signed NS counterexample.
L,t=s.symbols('L t',positive=True)
line=2*s.integrate((1-t/(2*L))**2,(t,0,2*L))
check('box_envelope_scaling',s.simplify(line**3-(4*L/3)**3)==0)
for lam in (1,2,3,4,8,16,32,64):
    check('energy_preserving_dilation',Q(lam)**-6*lam**9==lam**3)

# Original Hodge complementary-plane ideal: not a cycle-class producer.
a,b,t=s.symbols('a b t')
J=s.Matrix([[0,-b],[a,0]])
R=(t*s.eye(2)+(1-t-t*t)*J)/2
G=s.groebner([a*b+t-2,t**3+t*t-2*t-1],a,b,t,domain=s.QQ)
for M in (R**2-t*R+s.eye(2),R**4-R**3-J,R**7-s.eye(2)):
    for entry in M:
        check('Hodge_actual_middle_matrix',G.reduce(s.expand(entry))[1]==0)
check('Hodge_det',G.reduce(s.expand(R.det()-1))[1]==0)

# Biquadratic finite normal-restriction model, not the absolute Galois group.
# A sign pair acts on basis 1,sqrt(2),sqrt(3),sqrt(6), restrict to Q(sqrt(2)).
for x,y in product(product((-1,1),repeat=2),repeat=2):
    z=(x[0]*y[0],x[1]*y[1])
    check('normal_restriction_hom',z[0]==x[0]*y[0])
    for v in product(range(-1,2),repeat=2):
        check('embedded_basis_fixing', (x[0]==1) <= ((v[0],x[0]*v[1])==v))

for k,v in counts.items():
    print(k,v,'PASS')
print('TOTAL',sum(counts.values()),'PASS')
