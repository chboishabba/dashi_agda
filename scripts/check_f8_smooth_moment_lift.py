"""Smooth compact moment lift of the original monopole source.
Alternative consistent discretization, NOT baseline replacement or full TT weld.
"""
import json,hashlib
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import quad
from numpy.polynomial.legendre import leggauss
from ksw668_f8_fv_source_flux import exact_cell_averages


def check(work):
    r,h=s.symbols('r h',positive=True)
    mean=(r**4+r*r*h*h/2+h**4/80)/(r*r+h*h/12)
    assert s.factor(mean-r*r-5*h*h/12+h**4/(45*(r*r+h*h/12)))==0
    eps=.04;x,w=leggauss(96);target4=48*quad(lambda u:u*u*np.exp(1-1/(1-u*u)),0,1,epsabs=1e-13)[0]
    rows=[]
    with np.load(work/'ledger-far-e4-source-vjp.npz',allow_pickle=False) as z:
        k=z['grad'];assert hashlib.sha256(k.tobytes()).hexdigest()=='7a4ae45d9fc4c6cee2e884b63c8c634b68aedee70b26be9051ab540cddff9f9a'
    for dr in (.008,.006,.004,.003,.002,.001,.0005,.00025,.000125):
        r=np.arange(int(np.ceil(eps/dr))+2)*dr;g=exact_cell_averages(eps,r,dr)[0]
        a=np.maximum(r-dr/2,0);b=r+dr/2;vol=(b**3-a**3)/3
        idx=np.flatnonzero(np.minimum(b,eps)>a);a=a[idx]/eps;b=b[idx]/eps;vol=vol[idx];g=g[idx];hi=np.minimum(1,b)
        u=a[:,None]+(hi-a)[:,None]*(x+1)/2
        measure=w[None,:]*(hi-a)[:,None]/2*eps**3*u*u
        bump=np.exp(1-1/(1-u*u));basis=np.stack([np.sum(measure*bump*u**(2*j),axis=1)/vol for j in range(3)],axis=1)
        shell=np.stack([eps**3*(b**(3+2*j)-a**(3+2*j))/(3+2*j) for j in range(3)])
        nodal=np.stack([vol*(r[idx]/eps)**(2*j) for j in range(3)])
        for name,C,rank in [('nodal02',nodal,2),('shell02',shell,2),('shell024',shell,3)]:
            C=C[:rank];target=np.array([0.,0.,eps**3*target4])[:rank];B=basis[:,:rank];gram=C@B
            coeff=np.linalg.solve(gram,target-C@g);q=B@coeff;new=g+q
            residual=float(np.max(abs(C@new-target)));assert residual<1e-11
            row=dict(dr=dr,kind=name,relative_change=float(np.sqrt(vol@(q*q)/(vol@(g*g)))),coeff=coeff.tolist(),condition=float(np.linalg.cond(gram)),max_moment_residual=residual)
            if dr==.006:row['far_e4']=float(k[idx]@new)
            rows.append(row)
    return dict(shell_nodal_exact_identity=True,rows=rows)

if __name__=='__main__':
    import sys
    print(json.dumps(check(Path(sys.argv[1])),indent=2))
