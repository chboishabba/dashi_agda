from itertools import product
import sympy as s

def req(ok):
    if not ok: raise AssertionError('rank13 central completion')

n=12
R=s.zeros(n)
for j in range(n-1): R[j+1,j]=1
R[0,n-1]=-1
B=R**6
I=s.eye(n)
req(R**12==-I and R**24==I and B.T==-B and B**2==-I)
req(R.T*B*R==B and B.det()==1)
# Rational/integer identities imply the identities after reduction mod 3.
x=s.Matrix(s.symbols('x:12')); y=s.Matrix(s.symbols('y:12')); z=s.Matrix(s.symbols('z:12'))
def b(u,v): return (u.T*B*v)[0]
req(s.expand(b(x,y)+b(x+y,z)-b(y,z)-b(x,y+z))==0)
req(s.expand(b(R*x,R*y)-b(x,y))==0)
req(s.expand(b(x,x))==0)
# Antipode cannot negate the centre of this nonabelian group.
req(b(-I[:,0],-I[:,6])==b(I[:,0],I[:,6])!=0)
# Finite source profiles: 12 axes and one shared centre. Signed spatial
# codec uses 12 oriented unit representatives and one pole representative.
def shift(v): return ((-v[-1])%3,)+v[:-1]
def unshift(v): return v[1:]+((-v[0])%3,)
def pair(v,w): return sum(v[j+6]*w[j]-v[j]*w[j+6] for j in range(6))%3

def encode(v,c): return v+(c,)+tuple(-t%3 for t in v)+( -c%3,0)
def decode(w):
    req(len(w)==27 and w[-1]==0 and all((w[j]+w[j+13])%3==0 for j in range(13)))
    return w[:12],w[12]
count=0
for v in product(range(3),repeat=12):
    req(unshift(shift(v))==v)
    for c in range(3):
        req(decode(encode(v,c))==(v,c)); count+=1
req(count==3**13)
# Group law (v,c)*(w,d)=(v+w,c+d+2*B(v,w)).
def add(v,w): return tuple((a+b)%3 for a,b in zip(v,w))
def law(a,b):
    v,c=a; w,d=b
    return add(v,w),(c+d+2*pair(v,w))%3

def action(a): return shift(a[0]),a[1]
def spatial(a): return tuple(-t%3 for t in a[0]),-a[1]%3
basis=[tuple(int(i==j) for i in range(n)) for j in range(n)]
zero=(0,)*n
probes=[(v,c) for v in [zero]+basis+[tuple(-t%3 for t in v) for v in basis] for c in range(3)]
for a,b0 in product(probes,repeat=2): req(action(law(a,b0))==law(action(a),action(b0)))
a=(basis[0],0); b0=(basis[6],0)
req(spatial(law(a,b0))!=law(spatial(a),spatial(b0)))
req(law(a,b0)!=law(b0,a))
# Every nonzero v has a nonzero commutator with a basis vector by B invertibility.
print(f'PASS {count} signed profile round trips; {len(probes)**2} automorphism pairs; symbolic cocycle, rank12 form, spatial-centre negative control')
