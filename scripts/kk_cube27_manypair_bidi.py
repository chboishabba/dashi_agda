"""Native open Cube27, fixed-number bosons. Dimensionless selected model."""
from check_369_cube27_geometry_vs_modular_charge import CUBE, edges
from check_smith_filsinger_dispersive_port_symbolic import nonlinear_material
from itertools import combinations_with_replacement
import numpy as np
from scipy.sparse import coo_matrix, diags
from scipy.sparse.linalg import eigsh, cg, LinearOperator
from math import comb

def operators(N,U,J,flux):
    sites=sorted(CUBE); ix={p:i for i,p in enumerate(sites)}
    states=list(combinations_with_replacement(range(27),N)); index={x:i for i,x in enumerate(states)}
    bonds=[(ix[p],ix[q],flux*p[0]*(q[1]-p[1])) for p,q in sorted(edges)]
    rows=[];cols=[];vals=[]; charging=[];dip=[];shape=[]
    for k,state in enumerate(states):
        occ=np.bincount(state,minlength=27)
        charging.append(sum(occ*(occ-1))/2)
        dip.append(sum(sites[i][2] for i in state))
        shape.append(sum(sites[i][2]*occ[i]*(occ[i]-1)/2 for i in range(27)))
        for i,j,a in bonds:
            for src,dst,phase in ((i,j,a),(j,i,-a)):
                if occ[src]:
                    x=list(state);x.remove(src);x.append(dst)
                    rows.append(index[tuple(sorted(x))]);cols.append(k)
                    vals.append(-J*np.exp(1j*phase)*np.sqrt(occ[src]*(occ[dst]+1)))
    Q=diags(charging); H=coo_matrix((vals,(rows,cols)),shape=(len(states),)*2).tocsr()+U*Q
    assert len(states)==comb(N+26,26)
    assert np.max(np.abs((H-H.getH()).data),initial=0)<1e-12
    return H,Q,np.asarray(dip),np.asarray(shape)

def solve(H,O,Q,S,U):
    e,w=eigsh(H,k=2,which='SA',tol=1e-11,v0=np.ones(H.shape[0]));order=np.argsort(e);e=e[order];g=w[:,order[0]]
    gap=e[1]-e[0]; assert gap>1e-7
    def project(v):return v-g*np.vdot(g,v)
    def mv(v):return H@v-e[0]*v+g*np.vdot(g,v)
    A=LinearOperator(H.shape,matvec=mv,dtype=complex)
    b=project(O*g); x,info=cg(A,b,rtol=1e-10,maxiter=2000);assert info==0
    chi=2*np.vdot(b,x).real
    mixed=2*np.vdot(project(-1.5*U*(Q@g)),x).real
    anis=2*np.vdot(project(-1.5*U*S*g),x).real
    assert abs(mixed)<1e-7
    step=0.002
    def energy(h):return eigsh(H+h*diags(O),k=1,which='SA',return_eigenvectors=False,tol=1e-12,v0=g)[0]
    fd=-(energy(step)+energy(-step)-2*e[0])/step**2
    assert abs(fd-chi)<1e-4*max(1,chi)
    return gap,chi,anis,fd
if __name__=='__main__':
    nonlinear_material()
    print('Filsinger nonlinear material identity PASS')
    for N in (1,2,3):
        for U in (0,1,4):
            for flux in (0,1.5):
                H,Q,O,S=operators(N,U,1,flux)
                print(N,U,flux,H.shape[0],*solve(H,O,Q,S,U),flush=True)
    print('PASS native cube sparse interacting sectors, reduced resolvent, independent finite difference, uniform and anisotropic vertices')
