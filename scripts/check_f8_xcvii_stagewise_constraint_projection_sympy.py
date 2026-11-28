"""F8 XCVII — source-equivalent candidate strong face closure, not a production patch.

Original normal_order=3 one-sided characteristic SAT, frozen-coefficient
normal subsystem, exact SymPy / Fraction SSPRK3 three-stage control.
No radial/warp forcing, moving-clock error, coupled energy or full receiver.
The action-Galerkin and weighted SBP4 constructors retain their ownership.
No GitHub CI or physical/continuum acceptance.
"""
import json
from fractions import Fraction as R
import sympy as s

def stage(U,P,M,v,h,A):
    n=len(U);a=1+v;c=1-v
    ud=[(a*P[i]+c*M[i])/2 for i in range(n)]
    pd=[];md=[]
    for i in range(n):
        if i==0:
            py=(P[1]-P[0])/h;my=(M[1]-M[0])/h
        elif i==n-1:
            py=(P[-1]-P[-2])/h;my=(M[-1]-M[-2])/h
        else:
            py=(P[i+1]-P[i-1])/(2*h);my=(M[i+1]-M[i-1])/(2*h)
        pi=a*py;mi=-c*my
        if i==n-1:pi-=2*a*P[i]/h
        if i==0:
            target=(2*A-a*P[0])/(v-1)
            mi+=2*c*(target-M[0])/h
        pd.append(pi);md.append(mi)
    return ud,pd,md

def constraints(U,P,M,h):
    n=len(U);out=[]
    for i in range(n):
        if i==0:q=(U[1]-U[0])/h
        elif i==n-1:q=(U[-1]-U[-2])/h
        else:q=(U[i+1]-U[i-1])/(2*h)
        out.append((P[i]-M[i])/2-q)
    return out

def project(U,P,M,v,h,A):
    assert v!=0
    P=P.copy();M=M.copy()
    q0=(U[1]-U[0])/h;qn=(U[-1]-U[-2])/h
    a=1+v;c=1-v
    P[0]=(A-c*q0)/v;M[0]=(A-a*q0)/v
    P[-1]=R(0);M[-1]=-2*qn
    assert (a*P[0]-c*M[0])/2==A
    assert P[-1]==0
    return U,P,M

def combine(x,y,a,b):
    return [a*xi+b*yi for xi,yi in zip(x,y)]

def rk3(U,P,M,dt,v,h,A,project_faces=False):
    state=(U,P,M)
    if project_faces:state=project(*state,v,h,A)
    snapshots=[constraints(*state,h)]
    k=stage(*state,v,h,A)
    s1=tuple(combine(state[i],k[i],R(1),dt) for i in range(3))
    if project_faces:s1=project(*s1,v,h,A)
    snapshots.append(constraints(*s1,h))
    k=stage(*s1,v,h,A)
    s2=tuple(combine(state[i],combine(s1[i],k[i],R(1),dt),R(3,4),R(1,4)) for i in range(3))
    if project_faces:s2=project(*s2,v,h,A)
    snapshots.append(constraints(*s2,h))
    k=stage(*s2,v,h,A)
    s3=tuple(combine(state[i],combine(s2[i],k[i],R(1),dt),R(1,3),R(2,3)) for i in range(3))
    if project_faces:s3=project(*s3,v,h,A)
    snapshots.append(constraints(*s3,h))
    return snapshots,s3

def audit():
    v,q,A=s.symbols("v q A",real=True,nonzero=True)
    a=1+v;c=1-v
    mat=s.Matrix([[s.Rational(1,2),-s.Rational(1,2)],[a/2,-c/2]])
    assert s.simplify(mat.det()-v/2)==0
    pp=(A-c*q)/v;mm=(A-a*q)/v
    assert s.simplify((pp-mm)/2-q)==0
    assert s.simplify((a*pp-c*mm)/2-A)==0
    # No uniform bound on |1/v| as v approaches zero.
    assert s.limit(-1/v,v,0,dir="-")==s.oo
    t=s.symbols("t",positive=True)
    vt=-1/s.sqrt(1+t*t)
    assert s.simplify(-1/vt-s.sqrt(1+t*t))==0
    n=4;z=([R(0)]*n,[R(0)]*n,[R(0)]*n)
    base,_=rk3(*z,R(1,100),R(-3,5),R(1,10),R(1),False)
    fixed,_=rk3(*z,R(1,100),R(-3,5),R(1,10),R(1),True)
    assert [x[0] for x in base]==[R(0),R(1,5),R(21,250),R(1591,9375)]
    assert all(all(qi==0 for qi in row) for row in fixed)
    assert base[-1][0]!=0
    return dict(status="PASS exact symbolic and rational construction-subsystem tests",
                boundary_map_determinant="v/2",
                original_lower_wall_Q_stages=[str(x[0]) for x in base],
                projected_all_Q_stages=[[str(v) for v in x] for x in fixed],
                velocity_inverse_condition="1/|v(t)|=sqrt(1+t²) (grows unbounded as t->infinity)",
                limitations="Candidate face projection; not production mode3 patch, spatial/warp/moving coefficient evolution, coupled energy stability, source-causal-null or Weyl convergence.")
if __name__=="__main__":
    print(json.dumps(audit(),indent=2))
