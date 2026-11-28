"""BR279: nodal adjoint of original material Hamiltonian and volume entropy.
Actual one-way material trajectory; not an Einstein source or coupled evolution.
"""
import inspect
from itertools import product
import numpy as np
from numpy.polynomial.legendre import leggauss
import check_hopf369_br241_metric_consumer as mat
from check_hopf369_br277_278_actual_reciprocal import assembly
from check_hopf369_br240_metric_history import run


def quadrature(g):
    z=mat.donor.z; n=g.shape[0]; dx=3/(n-1); t,w=leggauss(3);t=(t+1)/2;w=w/2
    def read(X):
        f=(X+1.5)/dx; i=np.floor(f).astype(int);f=f-i
        ids=[tuple(i+j) for j in product((0,1),repeat=3)]
        weights=[np.prod(np.where(j,f,1-f)) for j in product((0,1),repeat=3)]
        G=sum(a*g[idx][:4,:4] for a,idx in zip(weights,ids));return G,ids,weights
    for p in z.cells:
        for ijk in product(range(3),repeat=3):
            X=t[list(ijk)];e,b=z.basis(p,X);G,ids,weights=read(np.array(p)+X-1)
            yield G,ids,weights,np.prod(w[list(ijk)]),e,b,None
    bounds=[(-1,-.5),(-.5,.5),(.5,1)]
    for i,p in enumerate(z.P):
        lo=np.array([bounds[k][0] for k in p]);width=np.array([bounds[k][1]-bounds[k][0] for k in p])
        for ijk in product(range(3),repeat=3):
            G,ids,weights=read(lo+width*t[list(ijk)])
            yield G,ids,weights,np.prod(w[list(ijk)]*width),None,None,i


def geometry(G):
    h=G[1:,1:];I=np.linalg.inv(h); beta=I@G[0,1:];alpha=np.sqrt(beta@h@beta-G[0,0]);r=np.sqrt(np.linalg.det(h));return h,I,beta,alpha,r


def adjoint(g,x,amount):
    M=np.zeros((54,54));Ma=M.copy();L=np.zeros((54,36));V=np.full(33,4.);V[:27]=0
    records=list(quadrature(g)); N=np.zeros((36,36))
    for G,ids,weights,wt,e,b,i in records:
        h,I,beta,alpha,r=geometry(G)
        if i is not None:V[i]+=wt*r;continue
        W=r*I;M+=wt*e.T@W@e;Ma+=wt*alpha*e.T@W@e;L+=wt*(W@e).T@np.cross(beta,b.T).T;N+=wt*alpha*b.T@(h/r)@b
    y=np.linalg.solve(M,x[:54]);B=x[54:];z=np.linalg.solve(M,Ma@y+L@B)
    energy=.5*y@Ma@y+y@L@B+.5*B@N@B+np.sum(amount*(np.log(amount/V[:,None])-1))
    grad=np.zeros_like(g)
    for G,ids,weights,wt,e,b,i in records:
        h,I,beta,alpha,r=geometry(G);W=r*I
        if i is not None:
            local=np.zeros((4,4));local[1:,1:]=-amount[i].sum()/V[i]*r*I/2
        else:
            E=e@y;Z=e@z;Q=b@B;cross=np.cross(beta,Q);local=np.zeros((4,4))
            for a in range(4):
                for c in range(a,4):
                    U=np.zeros((4,4));U[a,c]=U[c,a]=1;dh=U[1:,1:];db=I@(U[0,1:]-dh@beta);da=(2*beta@U[0,1:]-beta@dh@beta-U[0,0])/(2*alpha);dr=r*np.trace(I@dh)/2
                    dW=dr*I-r*I@dh@I;dV=dh/r-h*dr/r**2
                    val=.5*E@(da*W+alpha*dW)@E+E@dW@cross+E@W@np.cross(db,Q)+.5*Q@(da*h/r+alpha*dV)@Q-Z@dW@E
                    local[a,c]=local[c,a]=val/(1+(a!=c))
        for idx,weight in zip(ids,weights):grad[idx][:4,:4]+=wt*weight*local
    return energy,grad


def main():
    gs,dx=run(11,full=True)
    def assemble(g):return assembly(g,np.zeros_like(g))[0],mat.assembly(g)[1]
    src=inspect.getsource(mat.material).replace('    dh=np.linalg.norm(H-Hstart);','    return x,n0\n    dh=np.linalg.norm(H-Hstart);')
    ns=dict(vars(mat),assembly=assemble,run=lambda *a,**kw:(gs,dx));exec(src,ns);x,amount=ns['material'](11)
    g=gs[-1];energy,grad=adjoint(g,x,amount)
    def direct(g):
        H,V=assemble(g);return .5*x@H@x+np.sum(amount*(np.log(amount/V[:,None])-1))
    assert abs(energy-direct(g))<1e-10
    rng=np.random.default_rng(369);d=rng.normal(size=g.shape);d=(d+d.swapaxes(-1,-2))/2;d[...,4,:]=d[...,:,4]=0;d*=.01
    for direction in (gs[-1]-gs[0],d):
        pred=np.sum(grad*direction);step=1e-4;fd=(direct(g+step*direction)-direct(g-step*direction))/(2*step);err=abs(pred-fd);assert err<1e-7
        print('BR279 nodal adjoint',pred,'FD',fd,'error',err,flush=True)
    assert np.max(abs(grad))>0 and np.all(grad[...,4,:]==0) and np.all(grad[...,:,4]==0)
    print('BR279 actual trajectory endpoint energy',energy,'nodal covector norm',np.linalg.norm(grad),flush=True)

if __name__=='__main__':main()
