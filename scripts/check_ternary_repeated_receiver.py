"""Multi-cycle source/receiver accounting on synthetic open ternary grids.

No claim of a stationary orbit, physical source calibration, optical dataset replay,
or global load optimum.  Shares the constitutive and incidence rules of
check_ternary_multistep_bidi.py from the current PR.
"""
import numpy as np
from scipy.optimize import root
from check_ternary_multistep_bidi import incidence, grad, storage

DT=.11; EPS=.85; MU=.9; ETA=.35

def trajectory(dim,beta,load,controller_amplitude,cycles=3):
    B=incidence(dim);nv,ne=B.shape
    E=np.linspace(-.2,.3,nv);H=np.linspace(.1,-.1,ne)
    P=np.linspace(-.03,.04,nv);a=np.full(nv,4.)
    initial=np.r_[E,H,P].copy()
    U0=storage(E,H,P,a,beta)
    totals=np.zeros(6) # natural,controller,material,load,relaxation,delta U
    max_res=0.
    for step in range(4*cycles):
        E0,H0,P0,a0=E.copy(),H.copy(),P.copy(),a.copy()
        a1=a0.copy()
        a1[nv//2]+=.07*(1 if step%2==0 else -1)
        jn=np.zeros(nv);jn[0]=.07
        jc=np.zeros(nv);jc[-1]=controller_amplitude*(1 if step%4 in (0,1) else -1)
        receiver=np.zeros(nv); receiver[-1]=1.
        def equations(z):
            E1,H1,P1=np.split(z,[nv,nv+ne])
            Em=(E0+E1)/2; Hm=(H0+H1)/2
            return np.r_[EPS*(E1-E0)+(P1-P0)-DT*(B@Hm+jn+jc-load*Em*receiver),
                         MU*(H1-H0)+DT*(B.T@Em),
                         ETA*(P1-P0)/DT+grad(P0,P1,a0,a1,beta)-Em]
        sol=root(equations,np.r_[E0,H0,P0],tol=1e-10)
        eq=float(np.max(np.abs(equations(sol.x))))
        assert eq<1e-9,(dim,beta,load,controller_amplitude,step,eq)
        E,H,P=np.split(sol.x,[nv,nv+ne]);a=a1
        Em=(E+E0)/2;dp=P-P0
        wn=DT*np.dot(Em,jn);wc=DT*np.dot(Em,jc)
        wm=np.dot(a-a0,P0*P0+P*P)/4
        wl=DT*load*Em[-1]**2
        loss=ETA*np.dot(dp,dp)/DT
        du=storage(E,H,P,a,beta)-storage(E0,H0,P0,a0,beta)
        r=du-wn-wc-wm+wl+loss
        assert abs(r)<1e-9,(dim,step,r)
        totals+=np.array([wn,wc,wm,wl,loss,du]);max_res=max(max_res,eq,abs(r))
    terminal=np.r_[E,H,P]
    telescoping=storage(E,H,P,a,beta)-U0
    assert abs(totals[5]-telescoping)<1e-9
    assert abs(totals[5]-sum(totals[:3])+totals[3]+totals[4])<1e-9
    # External supplied work includes signed natural and controller contributions.
    # Conservative debit excludes negative source work (outflow) and storage release.
    net=totals[3]-max(totals[0],0)-max(totals[1],0)-max(totals[2],0)-max(-totals[5],0)
    return dict(dim=dim,beta=beta,load=load,controller=controller_amplitude,
                source_work=totals[0],controller_work=totals[1],modulation_work=totals[2],
                useful_work=totals[3],dissipation=totals[4],storage_delta=totals[5],
                conservative_net=net,storage_reset_error=float(np.linalg.norm(terminal-initial)),
                maximal_residual=max_res)

def main():
    count=0
    for dim in (2,3):
        for beta in (0.,.45):
            rows=[trajectory(dim,beta,load,ctrl) for load in (.05,.18,1.0) for ctrl in (0.,.04)]
            for r in rows:
                assert r['maximal_residual']<1e-9;count+=1
                assert r['useful_work']>=0 and r['dissipation']>=0;count+=1
                assert np.isfinite(r['conservative_net']);count+=1
            best=max(rows,key=lambda row:row['conservative_net'])
            print(f'{dim}D beta={beta} 6-point winner load={best["load"]} control={best["controller"]} net={best["conservative_net"]:.8g} storage_delta={best["storage_delta"]:.8g} reset_error={best["storage_reset_error"]:.8g} max_res={max(r["maximal_residual"] for r in rows):.3g}')
    print(f'{count}/{count} fixture assertions PASS across 24 three-cycle trajectories (288 independent midpoint steps)')
if __name__=='__main__':main()
