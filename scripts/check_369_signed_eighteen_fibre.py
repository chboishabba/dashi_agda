from itertools import product
import sympy as s

T=(-1,0,1)
succ={-1:0,0:1,1:-1}
pred={v:k for k,v in succ.items()}
D={x for x in product(T,repeat=3) if len(set(x))==2}
E=set(product(T,(-1,1),T))
def encode(x):
    a=next(v for v in T if x.count(v)==2)
    b=next(v for v in x if v!=a)
    return a,1 if b==succ[a] else -1,x.index(b)-1
def decode(y):
    a,o,j=y
    x=[a]*3
    x[j+1]=(succ if o==1 else pred)[a]
    return tuple(x)
assert {encode(x) for x in D}==E
assert all(decode(encode(x))==x for x in D)
assert all(encode(tuple(-v for v in x))==(-encode(x)[0],-encode(x)[1],encode(x)[2]) for x in D)
z=s.symbols('z')
red=lambda q:s.rem(s.expand(q),z*z+z+1,z)
r=[z+s.Rational(1,3),z*z+s.Rational(1,3),s.Rational(1,3)]
assert red(sum(r))==0
conj=lambda q:red(q.subs(z,z*z))
assert red(sum(v*conj(v) for v in r))==s.Rational(5,3)
print(s.__version__,len(D),'roundtrips and sign PASS; centred norm 5/3')
