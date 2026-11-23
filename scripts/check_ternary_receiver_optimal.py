"""Bounded receiver optimisation with separately declared source and signed work.

Synthetic 3^d open Cartesian model; no Earth/optical physical parameters.
Reuses the repository's nonlinear material, incidence and storage definitions.
"""
import numpy as np
from scipy.optimize import root, minimize_scalar
from check_ternary_multistep_bidi import incidence, grad, storage

DT=.11; EPS=.85; MU=.9; ETA=.35

def simulate(dim,beta,control,load):
    B=incidence(dim); nv,ne=B.shape
    E0=np.linspace(-.2,.3,nv); H0=np.linspace(.1,-.1,ne)
    P0=np.linspace(-.03,.04,nv); a=np.full(nv,4.)
    jn=np.zeros(nv); jn[0]=.07
    jc=np.zeros(nv); jc[-1]=control
    receiver=np.zeros(nv); receiver[-1]=1
    def residual(z):
        E1,H1,P1=np.split(z,[nv,nv+ne]);Em=(E0+E1)/2;Hm=(H0+H1)/2
        return np.r_[EPS*(E1-E0)+(P1-P0)-DT*(B@Hm+jn+jc-load*Em*receiver),
                     MU*(H1-H0)+DT*B.T@Em,
                     ETA*(P1-P0)/DT+grad(P0,P1,a,a,beta)-Em]
    result=root(residual,np.r_[E0,H0,P0],tol=1e-10)
    assert max(abs(residual(result.x)))<1e-9
    E1,H1,P1=np.split(result.x,[nv,nv+ne]);Em=(E0+E1)/2;Hm=(H0+H1)/2
    natural=DT*np.dot(Em,jn); controller=DT*np.dot(Em,jc)
    useful=DT*load*Em[-1]**2
    relax=ETA*np.dot(P1-P0,P1-P0)/DT
    du=storage(E1,H1,P1,a,beta)-storage(E0,H0,P0,a,beta)
    ledger=du-natural-controller+useful+relax
    assert abs(ledger)<1e-9
    return dict(useful=float(useful),natural=float(natural),controller=float(controller),
                relaxation=float(relax),storage=float(du),ledger=float(ledger),
                receiver=float(Em[-1]))

def optimize(dim,beta):
    # Separate useful-load work from controller and storage-release costs.
    def net(z):
        r=simulate(dim,beta,*z)
        return r['useful']-max(r['controller'],0)-max(-r['storage'],0)
    fixed=.04
    opt_load=minimize_scalar(lambda load:-simulate(dim,beta,fixed,load)['useful'],
                             bounds=(.02,2.),method='bounded',options={'xatol':1e-7})
    assert opt_load.success
    load_star=float(opt_load.x); best=simulate(dim,beta,fixed,load_star)
    grid=[(float(c),float(L)) for c in np.linspace(0,.08,5) for L in np.linspace(.02,2.,7)]
    scan=max(grid,key=net); winner=simulate(dim,beta,*scan)
    baseline=simulate(dim,beta,fixed,.18)
    assert best['useful']>=baseline['useful']-1e-11
    assert net(scan)>=max(net(z) for z in grid)-1e-13
    assert all(abs(simulate(dim,beta,*z)['ledger'])<1e-9 for z in (scan,(fixed,load_star)))
    return dict(dim=dim,beta=beta,fixed_control=fixed,load_star=load_star,
                load_useful=best['useful'],baseline_useful=baseline['useful'],
                finite_scan_control=scan[0],finite_scan_load=scan[1],
                finite_scan_net=net(scan),natural=winner['natural'],
                controller=winner['controller'],storage=winner['storage'],
                finite_candidates=len(grid))

def main():
    for dim in (2,3):
        for beta in (0.,.45):
            print(optimize(dim,beta))
    print('PASS: 4 bounded load optimizations + 4 finite controller/load scans')
if __name__=='__main__':main()
