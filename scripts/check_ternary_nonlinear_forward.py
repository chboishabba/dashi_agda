"""Synthetic 3^d Cartesian midpoint Maxwell/material system, d=2,3.

Reference open-grid incidence, not a measured apparatus or physical Hodge weld.
The local nonlinear constitutive law comes from the distributed-line donor.
"""
import numpy as np
from scipy.optimize import root
from check_ternary_cubical_ledger import boundary


def energy(E,H,P,a,eps,mu,beta):
    return (eps*np.dot(E,E)+mu*np.dot(H,H)+np.dot(a,P*P))/2 + beta*np.sum(P**4)/4


def discrete_gradient(P0,P1,a0,a1,beta):
    return (a0+a1)*(P0+P1)/4 + beta*(P0+P1)*(P0*P0+P1*P1)/4


def solve(d,modulated=True,beta=0.45):
    B=np.array(boundary(d,1),dtype=float)
    nv,ne=B.shape
    dt=0.11; eps=0.85; mu=0.9; eta=0.35
    E0=np.linspace(-.2,.3,nv); H0=np.linspace(.1,-.1,ne)
    P0=np.linspace(-.03,.04,nv)
    a0=np.full(nv,4.0)
    a1=a0.copy()
    if modulated: a1[nv//2: nv//2+1] += .3
    # Independent toy natural/controller inputs are declared and accounted for.
    jn=np.zeros(nv); jn[0]=.07
    jc=np.zeros(nv); jc[nv//2]=-.03
    def equations(x):
        E1=x[:nv]; H1=x[nv:nv+ne]; P1=x[nv+ne:]
        Em=(E0+E1)/2; Hm=(H0+H1)/2
        rE=eps*(E1-E0)+(P1-P0)-dt*(B@Hm+jn+jc)
        rH=mu*(H1-H0)+dt*(B.T@Em)
        rP=eta*(P1-P0)/dt+discrete_gradient(P0,P1,a0,a1,beta)-Em
        return np.concatenate([rE,rH,rP])
    sol=root(equations,np.r_[E0,H0,P0],tol=1e-11)
    if not sol.success and np.max(np.abs(equations(sol.x)))>1e-10:
        raise AssertionError(sol.message)
    E1=sol.x[:nv]; H1=sol.x[nv:nv+ne]; P1=sol.x[nv+ne:]
    Em=(E0+E1)/2; Hm=(H0+H1)/2; dp=P1-P0
    du=energy(E1,H1,P1,a1,eps,mu,beta)-energy(E0,H0,P0,a0,eps,mu,beta)
    wn=dt*np.dot(Em,jn); wc=dt*np.dot(Em,jc)
    wm=np.dot(a1-a0,(P0**2+P1**2))/4
    q=eta*np.dot(dp,dp)/dt
    residual=du-wn-wc-wm+q
    r=equations(sol.x)
    split=np.dot(Em,r[:nv])+np.dot(Hm,r[nv:nv+ne])+np.dot(dp,r[nv+ne:])
    return dict(d=d,vertices=nv,edges=ne,max_equation_residual=float(np.max(np.abs(r))),
                energy_residual=float(residual),off_solution_identity=float(residual-split),
                natural_work=float(wn),controller_work=float(wc),modulation_work=float(wm),
                relaxation=float(q),storage_delta=float(du))


def run():
    count=0
    for d in (2,3):
        for mod in (False,True):
            for beta in (0.0,.45):
                row=solve(d,mod,beta)
                assert row['max_equation_residual']<1e-10; count+=1
                assert abs(row['energy_residual'])<1e-10; count+=1
                assert abs(row['off_solution_identity'])<1e-10; count+=1
                assert row['relaxation']>=0; count+=1
                if not mod:
                    assert abs(row['modulation_work'])<1e-14; count+=1
                print(row)
    print(f'{count}/{count} PASS: independent forward root + energy ledger')

if __name__=='__main__':
    run()
