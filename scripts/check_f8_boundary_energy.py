"""Derivative-free inhomogeneous wall energy for original scalar F8.
Symmetric multiplier, certified local generalized-eigenvalue upper bound.
"""
import json
from fractions import Fraction as Q
from check_f8_local_dual_weld import I


def matrices(box,k,theta,reverse,wall):
    b=I(*box[0]);v=-b/(1+b*b).sqrt();s=1/(1+b*b);a=b/(1+b*b)**2
    if reverse:v=-v
    zinv=1/b if wall else I(0);c=3*v*zinv/2;t=Q(theta);u=s.sqrt()
    H=[[I(1),I(),I()],[I(),1+t*v,t*u],[I(),t*u,1-t*v]]
    o=(a-2*v*c)/(2*u);d=a+3*zinv
    S=[[-c,-t*k*v/2,-t*k*u/2],[-t*k*v/2,c+t*d/2,o-t*v*d/(2*u)],[-t*k*u/2,o-t*v*d/(2*u),-c-v*a/s+t*(a*(1+v*v)/s-3*zinv)/2]]
    return H,S


def rate(box,k,theta,reverse=False):
    # Floats propose a rate; exact interval Sylvester tests authorize it.
    import numpy as np
    from scipy.linalg import eigvalsh
    pairs=[matrices(box,k,theta,reverse,x) for x in (False,True)]
    mid=lambda a:np.array([[float((v.l+v.h)/2) for v in row] for row in a])
    r=max(float(eigvalsh(mid(S),mid(H))[-1]) for H,S in pairs);q=Q(max(0,int(r*10000)+1),10000);step=Q(1,10000)
    def positive(H,S,g):
        a,b,c=(g*H[0][i]-S[0][i] for i in range(3));d=g*H[1][1]-S[1][1];e=g*H[1][2]-S[1][2];f=g*H[2][2]-S[2][2]
        return a.l>0 and (a*d-b*b).l>0 and (a*d*f+2*b*c*e-a*e*e-d*c*c-f*b*b).l>0
    while not all(positive(H,S,q) for H,S in pairs):q+=step;step*=2
    return q


def check():
    import sympy as S
    v,a,z,k,t,W,N,g=S.symbols('v a z k theta W N g',real=True);s=1-v*v
    H=S.diag(1,1,s)+t*S.Matrix([[0,0,0],[0,v,s],[0,s,-v*s]])
    A=S.Matrix([[0,0,0],[0,2*v,s],[0,1,0]]);B=S.Matrix([[0,k,0],[-k,0,a-3/z],[0,0,0]])
    assert S.simplify(H*A-(H*A).T)==S.zeros(3)
    X=S.Matrix([0,W,(g-v*W)/s]);flux=S.factor((X.T*H*A*X)[0]/2)
    assert S.simplify(flux-(t*W*W/2+W*g+t*g*g/2))==0
    assert S.expand(t*W*W/2+W*g+t*g*g/2-t*(W+g/t)**2/2+(1-t*t)*g*g/(2*t))==0
    C=S.Matrix([[v,S.sqrt(s)],[S.sqrt(s),-v]]);assert S.simplify(C*C-S.eye(2))==S.zeros(2)
    M=(H.diff(v)*a-3*v/z*H+3/z*H*A+H*B+B.T*H)/2
    K=S.Matrix([[0,-k*v/2,-k*s/2],[-k*v/2,(a+3/z)/2,-v*(a+3/z)/2],[-k*s/2,-v*(a+3/z)/2,(a*(1+v*v)-3*s/z)/2]])
    assert S.simplify(M.diff(t)-K)==S.zeros(3)
    rows=[]
    for b in (Q(1),Q(1,2),Q(1,12)):
        box=((b,b),None,None,None)
        for th in (Q(1,32),Q(1,8),Q(1,4)):
            vals=[float(rate(box,I(1),th,r)) for r in (False,True)];rows.append([float(b),float(th),*vals])
    return dict(checks=23,rows=rows,scope='exact multiplier/boundary algebra and 18 rational generalized eigenvalue certificates')
if __name__=='__main__':print(json.dumps(check()))


def advance(B,h,k,box,R,G,theta,gamma):
    """Whole-slab H_theta norm bound. G must bound h*sup |g| (not merely L1)."""
    import check_f8_vector_interval as vi
    import numpy as np
    b,v,s,a=[vi.V.rational(*x) for x in box];t=vi.rat(theta);dt=vi.V(h)
    wall=(1-t.square())/(t*vi.V(b.l).square()*vi.V(b.l))
    q=vi.V(B).square()+wall*vi.V(G).square()/dt
    root=vi.V(np.maximum(q.l,0),q.h).sqrt()
    f=(1+t*vi.V(v.mag())).sqrt()*vi.V(R)
    den=1-dt*vi.rat(gamma);assert den.l>0
    return ((root+f)/den).h
