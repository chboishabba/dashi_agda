from itertools import product
import sympy as S
X=list(product(range(2),range(3),range(3),range(3)))
def chart(p): return (3*p[0]+p[1],p[2:])
def back(q): return (q[0]//3,q[0]%3,*q[1])
def r(p): return (p[0],(p[1]+1)%3,*p[2:])
def s(p): return (1-p[0],-p[1]%3,*p[2:])
def corrected(p):
    a,x,y,z=p
    return (a if (y,z)==(0,0) else 1-a,-x%3,y,z)
for p in X:
    assert back(chart(p))==p
    assert r(r(r(p)))==s(s(p))==corrected(corrected(p))==p
    assert s(r(s(p)))==corrected(r(corrected(p)))==r(r(p))
    a,(y,z)=chart(p)
    assert chart(r(p))==(3*(a//3)+(a%3+1)%3,(y,z))
    assert chart(s(p))==(3*(1-a//3)+(-(a%3))%3,(y,z))
assert sum(s(p)==p for p in X)==sum(r(p)==p for p in X)==0
assert sum(corrected(p)==p for p in X)==2
w=S.Symbol('w'); mod=w*w+w+1
F=S.Matrix(3,3,lambda k,x:w**((-k*x)%3))
R=S.Matrix(3,3,lambda i,j:int(i==(j+1)%3))
J=S.Matrix(3,3,lambda i,j:int(i==(-j)%3))
D=S.diag(1,w*w,w)
red=lambda M:M.applyfunc(lambda a:S.rem(S.expand(a),mod,w))
assert red(F*R-D*F)==S.zeros(3)
assert red(F*J-J*F)==S.zeros(3)
assert red(J*D*J-D**2)==S.zeros(3)
assert s((0,0,0,0))==(1,0,0,0)
print('PASS: 54 chart round trips, regular and corrected S3 actions, exact Fourier squares, deletion obstruction')
