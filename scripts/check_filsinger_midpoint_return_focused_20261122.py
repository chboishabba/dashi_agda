#!/usr/bin/env python3
"""Source-conditioned Filsinger NST M vs separate tuned U-V coil return cut.
User-transcribed connection words are not a physical photographed pin map.
Ideal diode island, unloaded capacitive reference and linear loaded proxy.
"""
from sympy import Matrix, symbols, I, Rational as Q, simplify, conjugate, re, limit, oo
passed=[]
def eq(a,b): return simplify(a-b)==0
def test(label,expr):
    assert bool(expr),label
    passed.append(label)
# Only U/V->P diode currents leave a fully floating coil source island.
D=Matrix([[1,1,1,1]])
test('diode cut rank 1',D.rank()==1)
test('diode cut nullity 3',len(D.nullspace())==3)
for i in range(4):
    v=Matrix([int(j==i) for j in range(4)])
    test(f'diode package {i} crosses source cut positively',D*v==Matrix([1]))
E=Matrix([[1,1,0,0],[0,0,1,1]])
test('opposite node diode group rank 2',E.rank()==2)
test('opposite diode groups add to same outward cut',Matrix([[1,1]])*E==D)
a,b,c=symbols('a b c',nonnegative=True)
d=-(a+b+c)
test('no-return fourth current necessarily nonpositive',d.is_nonpositive)
for name,vals in [('a',{a:1,b:0,c:0}),('b',{a:0,b:1,c:0}),('c',{a:0,b:0,c:1})]:
    test(f'positive {name} requires forbidden reverse diode',d.subs(vals)<0)
test('all-zero diode current obeys island KCL',d.subs({a:0,b:0,c:0})==0)
# Capacitive/displacement return to M: U-V=e AC differential source.
Cu,Cv,G,w,e=symbols('Cu Cv G w e',positive=True,real=True)
s=I*w
A=Matrix([[G+s*Cu,s*Cv],[1,-1]])
U,V=A.inv()*Matrix([0,e])
ue=s*Cv*e/(G+s*(Cu+Cv))
ve=-(G+s*Cu)*e/(G+s*(Cu+Cv))
test('loaded floating U node formula',eq(U,ue))
test('loaded floating V node formula',eq(V,ve))
test('source differential U minus V',eq(U-V,e))
test('floating supernode KCL',eq((G+s*Cu)*U+s*Cv*V,0))
test('no V-to-M displacement return implies U=0',eq(limit(U,Cv,0,dir='+'),0))
test('unloaded cap divider U',eq(U.subs(G,0),e*Cv/(Cu+Cv)))
test('unloaded cap divider V',eq(V.subs(G,0),-e*Cu/(Cu+Cv)))
test('equal caps masquerade as hard +e/2',eq(U.subs({G:0,Cu:1,Cv:1}),e/2))
test('equal caps masquerade as hard -e/2',eq(V.subs({G:0,Cu:1,Cv:1}),-e/2))
test('load causes finite capacitive midpoint shift',not eq(U.subs({Cu:1,Cv:1,G:1,w:1}),e/2))
test('unbounded load lowers U to zero',eq(limit(U,G,oo),0))
# Source funding of the linear resistive proxy; no natural donor invented.
Is=-s*Cv*V
Pin=re(e*conjugate(Is))
Pload=G*U*conjugate(U)
test('source return KCL current',eq(Is,(G+s*Cu)*U))
test('signed real source funds resistive load',eq(Pin,Pload))
test('capacitor Cu mean real power zero',eq(re(U*conjugate(s*Cu*U)),0))
test('capacitor Cv mean real power zero',eq(re(V*conjugate(s*Cv*V)),0))
test('normalized useful load is 1/5',eq(Pload.subs({Cu:1,Cv:1,G:1,w:1,e:1}),Q(1,5)))
test('normalized source real power is 1/5',eq(Pin.subs({Cu:1,Cv:1,G:1,w:1,e:1}),Q(1,5)))
test('source current with G=0 is capacitive',eq((Is/e).subs(G,0),s*Cu*Cv/(Cu+Cv)))
test('unloaded differential source real power zero',eq(re((Is/e).subs(G,0)),0))
test('no displacement Cv means no source load work',eq(limit(Pin,Cv,0,dir='+'),0))
print(f'{len(passed)}/{len(passed)} exact SymPy return-path checks PASS')
