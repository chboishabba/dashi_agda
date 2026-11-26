"""Conditional signed Drude sideband and OCT369 tangent projection.
Convention exp(-i omega t), matching collision_tensor. No calibrated heating.
"""
import numpy as np
import sympy as s
from itertools import product

def sideband(nu,gyro,b,D,dnu,dD,w,v,E):
    b=np.asarray(b); J=np.cross(b,np.eye(3)).T
    A=lambda f:(nu-1j*f)*np.eye(3)+gyro*J
    j=np.linalg.solve(A(v),D*E)
    return np.linalg.solve(A(w+v),dD*E-dnu*j)

def shell(sites,weights,tensors):
    out=np.zeros((6,6),complex)
    for n,w,S in zip(sites,weights,tensors):
        n=np.asarray(n)/np.linalg.norm(n)
        B=np.sqrt(1.5)*np.column_stack((np.cross(n,np.eye(3)).T,np.eye(3)-np.outer(n,n)))
        out+=w*B.T@S@B
    return out

def inverse(A,y):
    x=np.linalg.lstsq(A,y,rcond=1e-12)[0]; return x,y-A@x

def fixtures():
    nu,o,D=s.symbols('nu o D',positive=True); J=s.Matrix([[0,-1],[1,0]]); A=nu*s.eye(2)+o*J
    assert (s.diff(D*A.inv(),nu)+D*A.inv()*A.inv()).applyfunc(s.simplify)==s.zeros(2)
    sites=[x for x in product((-1,0,1),repeat=3) if any(x)]; weights=[{1:1/21,2:4/105,3:9/280}[sum(t!=0 for t in x)] for x in sites]
    assert np.allclose(shell(sites,weights,[np.eye(3)]*26),np.eye(6))
    E=np.array([1.,2.,-1.]); b=np.array([0.,0.,1.]); worst=0.; count=0
    for f in (0,3.915,7.83,7800):
        for v in (0,7.83,-7.83):
            w=2*np.pi*f; v=2*np.pi*v
            j=sideband(2,-3,b,4,.2,.3,w,v,E)
            jj=sideband(2,-3,b,4,.2,.3,-w,-v,E)
            assert np.allclose(jj,j.conj()); count+=1
            assert np.allclose(sideband(2,-3,b,4,.2,.3,w,v,E*0),0)
            if w==0:
                Jn=np.cross(b,np.eye(3)).T
                fun=lambda t:np.linalg.solve((2+.2*t-1j*v)*np.eye(3)-3*Jn,(4+.3*t)*E)
                err=np.linalg.norm(j-(fun(1e-5)-fun(-1e-5))/2e-5); worst=max(worst,err); assert err<1e-8
    A=np.array([[1,0],[0,1],[0,0]],complex); x,r=inverse(A,np.array([1,2,3])); assert np.allclose(A.conj().T@r,0) and np.linalg.norm(r)==3
    print(dict(signed_cases=count,max_derivative_error=worst,physical_admission=False))
if __name__=='__main__': fixtures()
