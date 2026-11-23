"""Finite open ternary 3x3/3x3x3 nonlinear midpoint multi-step BIDI fixture."""
from itertools import combinations,product
import numpy as np
from scipy.optimize import root

def incidence(dim):
    vertices=list(product(range(3),repeat=dim))
    rows={v:i for i,v in enumerate(vertices)}
    edges=[(pt,axis) for axis in range(dim) for pt in product(*(range(2 if j==axis else 3) for j in range(dim)))]
    B=np.zeros((len(vertices),len(edges)))
    for c,(pt,axis) in enumerate(edges):
        dst=list(pt);dst[axis]+=1
        B[rows[pt],c]=-1
        B[rows[tuple(dst)],c]=1
    return B

def storage(E,H,P,a,beta):
    return (.85*np.dot(E,E)+.9*np.dot(H,H)+np.dot(a,P*P))/2+beta*np.sum(P**4)/4

def grad(P0,P1,a0,a1,beta):
    return (a0+a1)*(P0+P1)/4+beta*(P0+P1)*(P0*P0+P1*P1)/4

def evolve(dim,beta,steps=4):
    B=incidence(dim);nv,ne=B.shape;dt=.11;eta=.35
    E=np.linspace(-.2,.3,nv);H=np.linspace(.1,-.1,ne)
    P=np.linspace(-.03,.04,nv);a=np.full(nv,4.)
    start=storage(E,H,P,a,beta);tot=np.zeros(5)
    for k in range(steps):
        E0,H0,P0,a0=E.copy(),H.copy(),P.copy(),a.copy()
        a1=a0.copy();a1[nv//2]+=.07*(1 if k%2==0 else -1)
        jn=np.zeros(nv);jn[0]=.07*(1+k/10)
        jc=np.zeros(nv);jc[nv//2]=-.03*(1 if k%2==0 else -1)
        def residual(x):
            E1,H1,P1=np.split(x,[nv,nv+ne])
            Em=(E0+E1)/2;Hm=(H0+H1)/2
            rE=.85*(E1-E0)+(P1-P0)-dt*(B@Hm+jn+jc)
            rH=.9*(H1-H0)+dt*(B.T@Em)
            rP=eta*(P1-P0)/dt+grad(P0,P1,a0,a1,beta)-Em
            return np.r_[rE,rH,rP]
        sol=root(residual,np.r_[E0,H0,P0],tol=1e-11)
        assert np.max(np.abs(residual(sol.x)))<1e-10
        E,H,P=np.split(sol.x,[nv,nv+ne]);a=a1
        Em=(E0+E)/2;Hm=(H0+H)/2;dp=P-P0
        total=(.85*(E-E0)+dp)/dt-B@Hm
        assert np.max(np.abs(total-jn-jc))<1e-10
        shift=np.zeros(nv);shift[0]=.02
        assert np.max(np.abs(total-(jn+shift)-(jc-shift)))<1e-10
        wn=dt*np.dot(Em,jn);wc=dt*np.dot(Em,jc)
        wm=np.dot(a-a0,P0*P0+P*P)/4
        loss=eta*np.dot(dp,dp)/dt
        du=storage(E,H,P,a,beta)-storage(E0,H0,P0,a0,beta)
        assert abs(du-wn-wc-wm+loss)<1e-10
        tot+=np.array([wn,wc,wm,loss,du])
    assert abs(tot[4]-(storage(E,H,P,a,beta)-start))<1e-10
    assert abs(tot[4]-sum(tot[:3])+tot[3])<1e-10
    return float(abs(tot[4]-sum(tot[:3])+tot[3]))

def main():
    for dim in (2,3):
        for beta in (0.,.45):
            print(f'{dim}D beta={beta} cumulative residual {evolve(dim,beta):.3g}')
    print('PASS 16 forward steps, source reconstruction and energy receipts; 4 cumulative ledgers')
if __name__=='__main__':main()
