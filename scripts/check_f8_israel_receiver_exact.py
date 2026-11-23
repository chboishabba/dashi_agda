"""Exact symbolic source and receiver controls; native numerical parity separate."""
import sympy as s
Q=s.Rational
v,f,S,P,M,h,dy=s.symbols('v f S P M h dy', nonzero=True)
assert s.cancel(h*2*(1-v)/dy*((2*f*S-(1+v)*P)/(v-1)-M)-h*2*(1-v)/dy*((-(1+v)*P)/(v-1)-M)+4*h*f*S/dy)==0
A=s.Matrix([[1,2],[0,1]]);B=s.Matrix([[2,0],[3,1]]);C=s.Matrix([[1,-1],[2,3]])
I=s.eye(2); L=I/3+Q(2,3)*C*(Q(3,4)*I+B*A/4)
x=s.Matrix(s.symbols('x:2')); p=s.Matrix(s.symbols('p:2')); r=[s.Matrix(s.symbols('r%d:2'%i)) for i in []]
r=[s.Matrix(s.symbols('a:2')),s.Matrix(s.symbols('b:2')),s.Matrix(s.symbols('c:2'))]
y=x/3+Q(2,3)*(C*(Q(3,4)*x+(B*(A*x+r[0])+r[1])/4)+r[2]);p2=Q(2,3)*C.T*p;p1=B.T*p2/4
assert s.expand((p.T*y-(L.T*p).T*x-s.Matrix([[sum((u.T*w)[0] for u,w in zip((p1,p2/4,2*p/3),r))]]))[0])==0
q=[s.Matrix(s.symbols('q%d_0 q%d_1'%(i,i))) for i in range(4)]
states=[x]; inserts=[]
for i in range(3):
 z=s.Matrix(s.symbols('z%d_0 z%d_1'%(i,i)));inserts.append(z);states.append(L*states[-1]+z)
p=q[-1]; a=0
for i in reversed(range(3)):
 a+=(p.T*inserts[i])[0];p=q[i]+L.T*p
assert s.expand(sum((u.T*w)[0] for u,w in zip(q,states))-(p.T*x)[0]-a)==0
print(s.__version__, 'PASS 3 symbolic identities')
