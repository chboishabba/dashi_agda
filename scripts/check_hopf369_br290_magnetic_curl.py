"""Original Hopf potential as a commuting discrete curl; preserve source defect.
This changes the finite magnetic sampling, not the continuum P0H source.
"""
import argparse
import numpy as np
import check_hopf369_br283_284_g4_coupled as d
import check_hopf369_br287_289_g4_audit as audit


def initial(n):
    g,v,U,dx=original(n); x=np.linspace(-1.5,1.5,n);X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1)
    X0,X1,X2=np.moveaxis(X,-1,0);D=1+np.sum(X*X,axis=-1)
    A=2*d.src.EPS*np.stack([2*X0*X2-2*X1,2*X0+2*X1*X2,1-X0*X0-X1*X1+X2*X2],axis=-1)/D[...,None]**2
    # The same periodic centered operator used by BR283 induction, with
    # diagnostics restricted away from the frozen boundary.
    derivative=lambda a,i:audit.diff(a,i,dx)
    B=np.stack([derivative(A[...,2],1)-derivative(A[...,1],2),derivative(A[...,0],2)-derivative(A[...,2],0),derivative(A[...,1],0)-derivative(A[...,0],1)],axis=-1)
    div=lambda b:sum(derivative(b[...,i],i) for i in range(3))
    sl=(slice(2,-2),)*3; old=U[...,4:].copy();err=float(np.max(abs(B[sl]-old[sl])));before=float(np.max(abs(div(old)[sl])));after=float(np.max(abs(div(B)[sl])))
    # Keep original total energy and momentum; re-read admissible primitives.
    # This is NOT a re-solved discrete York/Hamiltonian constraint.
    U[...,4:]=B
    assert after<1e-12 and err>0; _,_,_,_,margin=d.matter(g,U);assert margin>0
    print('BR290 original potential curl source sampling difference',err,'initial divergence before/after',before,after,'margin',margin,flush=True)
    return g,v,U,dx

original=d.initial
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=2);p.add_argument('--dt',type=float,default=.002);a=p.parse_args();d.initial=initial;audit.run(a.n,a.steps,a.dt)
