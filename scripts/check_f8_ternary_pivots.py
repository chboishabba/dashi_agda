"""Exact rational Schur pivots of literal F8 consecutive history groups.
Recompute only the required local entries of the original signed approximant.
"""
import json,sys,math
from fractions import Fraction as Q
import numpy as np
import sympy as S
from check_f8_global_wall_kernel import clock,grid,interp
from check_f8_causal_block_inverse import I

def run(n,mode):
    dt,t,b,lo,hi,span=clock(n);b=b[::-1];lo=lo[::-1];hi=hi[::-1];h=1/128;k=mode*np.pi/3.012
    bs=[I(lo[j+1],hi[j]) for j in range(n)]
    def p(i,j):
        xi=bs[j];center=float((xi.l+xi.h)/2);dz=b[i+1]-b[j+1];lag=abs(i-j)*dt;A=lag+dz;B=lag-dz
        r=grid(center,k,h,int(A/h)+2,int(B/h)+2)
        return np.array(interp(r,np.array([A]),np.array([B]),h)).ravel()
    def entry(i,j):
        v=-b[j+1]/np.sqrt(1+b[j+1]**2);a=p(i,j);c=p(j,i)
        return Q(float(2*(c[2]-v*a[1]+1.5*a[0]/b[j+1])*dt))
    piv=[];defect=[];checks=0
    for j in range(0,n,3):
        m=min(3,n-j)
        if m==1:continue
        L=S.zeros(m);q=S.ones(1,m)/m;J=S.ones(m,1);R=S.zeros(m-1,m);P=S.zeros(m,m-1)
        for a in range(m):
            for c in range(a):L[a,c]=S.Rational(entry(j+a,j+c))
        for a in range(m-1):R[a,a]=1;R[a,m-1]=-1;P[:,a]=S.eye(m)[:,a]-J/m
        det=(R*(S.eye(m)-L)*P).det()
        if m==3:
            x,y,z=L[1,0],L[2,0],L[2,1];assert det==(3+x+y+z+x*z)/3
        else:assert det==1+L[1,0]/2
        assert det>0;checks+=1;piv.append(det)
        defect.extend(abs(x) for x in q*L*P)
    assert max(defect)>0
    return dict(n=n,mode=mode,exact_positive_pivots=checks,min_pivot=str(min(piv)),min_pivot_display=float(min(piv)),max_pivot_display=float(max(piv)),non_descent_witness=str(max(defect)),non_descent_display=float(max(defect)),scope='exact rational literal binary64 local blocks, not continuum operator; causality makes complement block lower block triangular')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),int(sys.argv[2])),indent=2))
