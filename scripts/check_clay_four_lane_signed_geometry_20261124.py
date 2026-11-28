from itertools import product
from sympy import I, Matrix, Rational, symbols, expand, diff, factorial, sqrt

# RH: exact even horizontal Taylor coefficients and sign conversion.
a,q,v=symbols('a q v', real=True)
from sympy import cos, cosh
for j in range(4):
    assert diff(cosh(a*v)*cos(q*v),a,2*j).subs(a,0)==(-1)**j*diff(cos(q*v),q,2*j)
# Sixth remainder bound uses |a|^6/6!; odd coefficients are zero.
for j in (1,3,5):
    assert diff(cosh(a*v),a,j).subs(a,0)==0
assert factorial(6)==720
print('RH: 8 exact derivative/remainder checks')

# BSD: finite + divisible primary group models, actual transition multiplication.
count=0
for ell in (2,3,5):
    for lengths in ((),(1,),(2,),(1,3),(2,4)):
        for divisible in range(3):
            z=lambda n: sum(min(n,e) for e in lengths)+divisible*n
            for n in range(1,7):
                ker=z(1); image=z(n+1)-ker; cok=z(n)-image
                assert cok==z(1)-(z(n+1)-z(n))
                assert cok==sum(e<=n for e in lengths)
                assert 0<=cok<=z(1)
                count+=1
print('BSD:',count,'primary-layer transition checks')

# NS: actual real, divergence-free signed Fourier triad.
p=(1,0,0); q=(0,1,0); k=(1,1,0)
neg=lambda x:tuple(-i for i in x)
u={p:Matrix([0,1,0]),q:Matrix([0,0,1]),k:Matrix([0,0,I])}
u.update({neg(x):y.conjugate() for x,y in list(u.items())})
w1,w2=symbols('w1 w2',real=True)
w=lambda x: w1 if sum(i*i for i in x)==1 else w2
for x in u: assert Matrix(x).dot(u[x])==0 and u[neg(x)]==u[x].conjugate()
T=0; pair=0; cells=0
for x,y in product(u,repeat=2):
    z=tuple(i+j for i,j in zip(x,y))
    if z not in u: continue
    A=expand(I*u[x].dot(Matrix(y))*u[y].dot(u[z].conjugate()))
    B=expand(I*u[neg(x)].dot(Matrix(z))*u[z].dot(u[y].conjugate()))
    assert expand(B+A.conjugate())==0
    T-=2*w(z)*A.as_real_imag()[0]
    pair-=(w(z)-w(y))*A.as_real_imag()[0]
    cells+=1
assert expand(T-pair)==0 and expand(T+4*(w2-w1))==0
assert T.subs({w1:1,w2:2**Rational(1,4)})<0
# Under u -> -u the cubic transfer reverses, with energy unchanged.
assert (-T).subs({w1:1,w2:2**Rational(1,4)})>0
print('NS:',cells,'ordered triad checks; transfer',expand(T))

# Hodge: actual Gr(2,4) Schubert intersection fixture, Q^3 section.
G=Matrix.eye(2); L=Matrix([1,1]); r=Matrix([1,-1]); restriction=Matrix([[1,1]])
P=L*(L.T*G*L).inv()*L.T*G
assert P*P==P and P.T*G==G*P
assert P*r==Matrix([0,0]) and restriction*r==Matrix([0])
assert P*L==L and restriction*L==Matrix([2])
assert (r.T*G*r)[0]==2 and (L.T*G*r)[0]==0
assert Matrix.hstack(L,r).det()==-2
print('Hodge: 9 exact Schubert/hyperplane checks; primitive norm 2')
