"""Constrained receiver-port BIDI on synthetic open 3x3 and 3x3x3.

Fixed independent source, explicitly measured controller current and resistive load.
The controlled target is a *toy* endpoint field, not a cavity/solar measurement.
"""
import numpy as np
from scipy.optimize import brentq, root
from check_ternary_multistep_bidi import incidence, grad, storage

DT=.11
EPS=.85
MU=.9
ETA=.35
LOAD=.18

def simulate(dim, beta, control):
    B=incidence(dim); nv, ne=B.shape
    E0=np.linspace(-.2,.3,nv)
    H0=np.linspace(.1,-.1,ne)
    P0=np.linspace(-.03,.04,nv)
    a=np.full(nv,4.)
    natural=np.zeros(nv); natural[0]=.07
    controller=np.zeros(nv); controller[-1]=control
    receiver=np.zeros(nv);receiver[-1]=1
    def residual(x):
        E1,H1,P1=np.split(x,[nv,nv+ne]);Em=(E0+E1)/2;Hm=(H0+H1)/2
        return np.r_[EPS*(E1-E0)+(P1-P0)-DT*(B@Hm+natural+controller-LOAD*Em*receiver),
                     MU*(H1-H0)+DT*B.T@Em,
                     ETA*(P1-P0)/DT+grad(P0,P1,a,a,beta)-Em]
    sol=root(residual,np.r_[E0,H0,P0],tol=1e-11)
    eq=np.max(np.abs(residual(sol.x)))
    assert eq<1e-10,(dim,beta,control,eq)
    E1,H1,P1=np.split(sol.x,[nv,nv+ne]);Em=(E0+E1)/2;Hm=(H0+H1)/2
    total=(EPS*(E1-E0)+(P1-P0))/DT-B@Hm+LOAD*Em*receiver
    assert np.max(np.abs(total-natural-controller))<1e-10
    wn=DT*np.dot(Em,natural)
    wc=DT*np.dot(Em,controller)
    useful=DT*LOAD*Em[-1]**2
    relax=ETA*np.dot(P1-P0,P1-P0)/DT
    du=storage(E1,H1,P1,a,beta)-storage(E0,H0,P0,a,beta)
    ledger=du-wn-wc+useful+relax
    assert abs(ledger)<1e-10,(dim,beta,control,ledger)
    return dict(output=float(Em[-1]),load=float(useful),natural=float(wn),controller=float(wc),
                relaxation=float(relax),delta=float(du),residual=float(eq),ledger=float(ledger))

def run():
    checks=0
    for dim in (2,3):
        for beta in (0.,.45):
            natural=simulate(dim,beta,0.)
            reference=simulate(dim,beta,.04)
            target=reference['output']
            # Physical instrumentation fixes controller port; reverse solve only
            # its bounded amplitude, with the independent source held fixed.
            f=lambda c:simulate(dim,beta,c)['output']-target
            recovered=brentq(f,-.1,.1,xtol=1e-12)
            answer=simulate(dim,beta,recovered)
            assert abs(answer['output']-target)<1e-10;checks+=1
            assert abs(recovered-.04)<1e-8;checks+=1
            assert abs(answer['ledger'])<1e-10;checks+=1
            assert abs(natural['ledger'])<1e-10;checks+=1
            # Negative control: signed natural-port work is actually negative
            # in this fixture; it cannot be reported as an energy source gain.
            assert answer['natural'] < 0 and answer['controller'] > 0
            assert answer['load'] > 0 and answer['relaxation'] >= 0
            checks+=1
            # The inverse feasible set under the one-control parametrization
            # is unique over the sampled admissible interval.
            samples=[simulate(dim,beta,c)['output'] for c in (-.1,-.05,0.,.05,.1)]
            assert all(x<y for x,y in zip(samples,samples[1:]));checks+=1
            print(f'{dim}D beta={beta}: control={recovered:.9f}, output={target:.7g}, '
                  f'load={answer["load"]:.8g}, controller_work={answer["controller"]:.8g}, '
                  f'natural_work={answer["natural"]:.8g}, residual={answer["ledger"]:.2g}')
    print(f'{checks}/{checks} receiver BIDI checks PASS')
if __name__=='__main__':run()
