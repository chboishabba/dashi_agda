import sympy as s

checks = 0

def check(condition):
    global checks
    if not condition:
        raise AssertionError('exact check failed')
    checks += 1

x, y, z = s.symbols('x y z', real=True)
D = 1 + x*x + y*y + z*z
B = 8*s.Matrix([2*x*z-2*y, 2*x+2*y*z, 1-x*x-y*y+z*z])/D**3

def curl(v):
    return s.Matrix([s.diff(v[2], y)-s.diff(v[1], z),
                     s.diff(v[0], z)-s.diff(v[2], x),
                     s.diff(v[1], x)-s.diff(v[0], y)])

check(s.simplify(sum(s.diff(v, a) for v, a in zip(B, (x,y,z)))) == 0)
F = B.cross(curl(B)).applyfunc(s.factor)
check(curl(F).subs({x:1,y:0,z:0}) == s.Matrix([-4,0,0]))
X,Y,u,t = s.symbols('X Y u t', real=True)
check(s.expand((X-Y)**2-(1-Y**2)*(X**2-1)-(X*Y-1)**2) == 0)
msq = Y*(X**2-1)*(1-Y)/(X-Y)**2
check(s.simplify(msq.subs(X,1/Y)-Y/(1+Y)) == 0)
check(s.limit(Y/(1+Y),Y,1,dir='-') == s.Rational(1,2))
J = s.integrate(u**3*(1-u)**3/(u*u+(1-u)**2),(u,0,1))
check(s.simplify(J-(s.pi/16-s.Rational(11,60))) == 0)
check(s.simplify(60*s.pi**2*J-s.pi**2*(15*s.pi-44)/4) == 0)
check(s.integrate(t**5*s.exp(-t),(t,0,s.oo)) == 120)
# Newton identity: ch_3 = (c1^3-3*c1*c2+3*c3)/6.
a,b,c=s.symbols('a b c')
c1=a+b+c; c2=a*b+a*c+b*c; c3=a*b*c
check(s.expand(c1**3-3*c1*c2+3*c3-a**3-b**3-c**3)==0)
# Finite cyclic model of restriction/corestriction; not an arithmetic Selmer computation.
for n in range(1,7):
    m=3**n
    check(all((3*a)%m in range(0,m,3) for a in range(m)))
    check(len({(3*a)%m for a in range(m)})==m//3)
print(f'{checks}/{checks} exact symbolic/model checks PASS')
