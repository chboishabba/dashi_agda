"""Numerical contracted Bianchi diagnostic on the F8 common-prepotential field.
Not a constraint certificate: finite differences of reconstructed Ricci jets.
"""
import numpy as np
from math import asinh,sqrt
from check_f8_common_prepotential import angular,evolve,make_evaluator,diagnostics


def bianchi(value,X,outer,inner):
    eta=np.diag([-1.,1,1,1,1]);z=X[-1];inv=z*z*eta
    def trQ(X):
        Q=diagnostics(value,X,inner)[1]
        return Q-eta*np.trace(eta@Q)/2
    A=trQ(X);E=np.eye(5)*outer
    d=np.array([(trQ(X+e)-trQ(X-e))/(2*outer) for e in E])
    B=np.zeros((5,5,5))
    for m,a,b in np.ndindex(5,5,5):B[m,a,b]=(-(a==m)*(b==4)-(a==b)*(m==4)+eta[m,b]*eta[a,4])/z
    C=np.array([d[m]-B[m].T@A-A@B[m] for m in range(5)])
    return np.linalg.norm(np.einsum('ak,akn->n',inv,C))

if __name__=='__main__':
    xyz,P=angular();F=lambda t:asinh(t)-sqrt(1+t*t)/t
    X=np.r_[F(11.8),2.52*np.array([2.,3.,6.])/7,1/11.8+.06]
    for common in (False,True):
        H,m=evolve(270,71,.0025,common);v=make_evaluator(H,m,common,xyz,P)
        print('common',common,'trace-reversed Q divergence',*[bianchi(v,X,h,h/10) for h in (1e-4,2e-4)],flush=True)
