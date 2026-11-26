#!/usr/bin/env python3
"""Exact rational-polynomial H06 affine and four quaternion chart identities."""
import sympy as s

def require(ok,label):
    if not bool(ok):raise RuntimeError(label)
def zero(M):return all(s.cancel(v)==0 for v in M)
a,b,c,d,e,f,g,h,r,t,o,u,v,p0,p1,q0,q1,i=s.symbols('a b c d e f g h r t o u v p0 p1 q0 q1 i',real=True)
P=s.Matrix([[a,b],[c,d]]);Q=s.Matrix([[e,f],[g,h]])
row=s.Matrix([[r,t]]);p=s.Matrix([p0,p1]);q=s.Matrix([q0,q1]);X=s.Matrix([u,v])
A=i*P.adjugate();alpha=row*A;origin=o-(alpha*p)[0]
require(s.expand(origin+(alpha*(p+P*X))[0]-o-i*P.det()*(row*X)[0])==0,'literal forward polynomial')
require(s.expand(origin+(alpha*X)[0]-o-(row*A*(X-p))[0])==0,'literal reverse polynomial')
require(zero(P*A-i*P.det()*s.eye(2)),'selected pivot rows')
# One generic two-pivot composition, valid for any pair of actual marks
# whose selected two-row matrices have nonzero determinant.
Pinv=P.inv();Qinv=Q.inv();first=row*Pinv;h1=o-(first*p)[0]
nextP=Q*Pinv;nextOrigin=q-nextP*p
second=first*nextP.inv();h2=h1-(second*nextOrigin)[0]
require(zero(second-row*Qinv),'direction cocycle')
require(s.cancel(h2-(o-(row*Qinv*q)[0]))==0,'offset cocycle')
# Reverse parameter map and forward parameter map agree on either chart.
require(zero(Pinv*((p+P*X)-p)-X),'parameter reopening')
require(zero(p+P*(Pinv*(X-p))-X),'parameter reclosing')
print('PASS affine forward/reverse, normalized pivot, two-pivot cocycle and parameter round trips',flush=True)
w,x,y,z=s.symbols('w x y z',real=True);quat=s.Matrix([w,x,y,z])
def rotation(q):
    w,x,y,z=q;N=q.dot(q)
    return s.Matrix([[N-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)], [2*(x*y+w*z),N-2*(x*x+z*z),2*(y*z-w*x)], [2*(x*z-w*y),2*(y*z+w*x),N-2*(x*x+y*y)]])/N
R=rotation(quat);N=quat.dot(quat)
Ds=[s.eye(3),s.diag(1,-1,-1),s.diag(-1,1,-1),s.diag(-1,-1,1)]
# Left multiply by inverse unit quaternion for each selected chart.
aligned=[quat,s.Matrix([x,-w,z,-y]),s.Matrix([y,-z,-w,x]),s.Matrix([z,y,-x,-w])]
for k,(D,q) in enumerate(zip(Ds,aligned)):
    T=D*R;den=1+s.trace(T)
    require(s.cancel(den-4*quat[k]**2/N)==0,'trace domain')
    require(zero(T-rotation(q)),'literal half-turn')
    recovered=s.Matrix([T[2,1]-T[1,2],T[0,2]-T[2,0],T[1,0]-T[0,1]])/den
    require(zero(recovered-q[1:,0]/q[0]),'actual matrix inverse')
    require(zero(D*rotation(s.Matrix([1,*recovered]))-R),'reclose actual rotation')
    require(D.T*D==s.eye(3) and D.det()==1,'proper half-turn')
require(zero(rotation(-quat)-R),'retained central spin sign')
for k in range(1,4):
    q=s.eye(4)[:,k];R0=rotation(q)
    require(1+s.trace(R0)==0 and 1+s.trace(Ds[k]*R0)==4,'scalar chart refusal')
print('PASS four trace domains, half-turn identities, matrix inverse and reclose, central sign and three scalar singularities',flush=True)
