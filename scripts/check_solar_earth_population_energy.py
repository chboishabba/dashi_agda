"""Conditional local cold-fluid population/current work; not a fitted atmosphere."""
import json
import sympy as s

m,n,S,R=s.symbols('m n S R',positive=True)
q=s.symbols('q',real=True,nonzero=True)
nu=s.symbols('nu',nonnegative=True)
v=s.Matrix(s.symbols('v:3',real=True)); b=s.Matrix(s.symbols('b:3',real=True))
E=s.Matrix(s.symbols('E:3',real=True)); B=s.Matrix(s.symbols('B:3',real=True))
j=n*q*v; D=n*q*q/m; K=m*n*v.dot(v)/2
ndot=S-R
# Momentum balance in a fixed inertial frame, stationary neutral background.
vdot=q*(E+v.cross(B))/m-nu*v+S*(b-v)/n
jdot=q*(ndot*v+n*vdot)
assert (jdot-(D*E+q*j.cross(B)/m-nu*j+q*(S*b-R*v))).applyfunc(s.simplify)==s.zeros(3,1)
kd=m*ndot*v.dot(v)/2+m*n*v.dot(vdot)
loss=m*n*nu*v.dot(v)+m*S*(b-v).dot(b-v)/2+m*R*v.dot(v)/2
birth=m*S*b.dot(b)/2
assert s.expand(kd-j.dot(E)-birth+loss)==0
assert s.expand(kd-(j.dot(jdot)/D-j.dot(j)*(q*q/m)*ndot/(2*D**2)))==0
# Finite source event: remove at the old mean velocity, then mix births.
a,c=s.symbols('a c',nonnegative=True); total=a+c
p=a*v+c*b
assert s.cancel((m*a*v.dot(v)+m*c*b.dot(b))/2-m*p.dot(p)/(2*total)-m*a*c*(v-b).dot(v-b)/(2*total))==0
# Exact fixed-population midpoint update with full magnetic cross term.
w=s.Matrix(s.symbols('w:3',real=True)); h=s.symbols('h',positive=True)
dv=h*(q*(E+w.cross(B))/m-nu*w)
assert s.expand(m*n*((w+dv/2).dot(w+dv/2)-(w-dv/2).dot(w-dv/2))/2-h*n*q*w.dot(E)+h*m*n*nu*w.dot(w))==0
# Zero-density charts: no division by n at empty state. Exact event ledger.
def event(n,v,r,c,b):
    assert 0<=r<=n and c>=0
    a=n-r; t=a+c; p=a*v+c*b
    out=p/t if t else s.zeros(3,1)
    loss=r*v.dot(v)/2+(a*c*(v-b).dot(v-b)/(2*t) if t else 0)
    assert t*out.dot(out)/2-n*v.dot(v)/2==c*b.dot(b)/2-loss
    return t,out,loss
v=s.Matrix([2,-1,3]); b=s.Matrix([0,0,0]); count=0
for n in map(s.Integer,range(5)):
    for r in map(s.Integer,range(int(n)+1)):
        for c in map(s.Integer,range(5)):
            for vb in (b,v,s.Matrix([-1,2,0])):
                event(n,v,r,c,vb); count+=1
# Equal initial/final density need not mean equal momentum or stored energy.
a=event(s.Integer(2),v,s.Integer(0),s.Integer(0),b)
z=event(s.Integer(2),v,s.Integer(1),s.Integer(1),b)
assert a[0]==z[0] and a[1]!=z[1] and z[2]>0
print(json.dumps(dict(status='CONDITIONAL_POPULATION_CURRENT_ENERGY',sympy=s.__version__,symbolic_identities=5,exact_event_fixtures=count,equal_density_turnover_negative_control=True,zero_density_chart=True,physical_admission=False),indent=2))
