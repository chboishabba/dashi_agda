"""Replay continuous piecewise-polynomial history trajectories.
The exporter is diagnostic; certificate replay requires independently
certified residual/coefficient bounds. Exact rational time grid supports
a final partial slab and arbitrary internal subdivisions.
"""
from fractions import Fraction as Q
from solar_steelman_history_residual import step

def replay(delay,T,slabs,initial=0,history=(0,0)):
    delay,T=Q(delay),Q(T)
    assert delay>0 and T>2*delay
    e=Q(initial);assert e>=0 and len(history)==2
    past=[(-2*delay,-delay,Q(history[0])),(-delay,Q(0),Q(history[1]))]
    assert min(p[2] for p in past)>=0
    t=Q(0);out=[]
    for rec in slabs:
        lo,hi,mu,b,c,rho,jump=map(Q,rec)
        assert lo==t and lo<hi<=T and hi-lo<=delay and jump>=0
        def delayed(k):
            l,h=lo-k*delay,hi-k*delay
            values=[v for a,b,v in past if a<h and b>l]
            assert values and h<=lo
            return max(values)
        e,s=step(hi-lo,mu,b,c,rho,e+jump,delayed(1),delayed(2))
        past.append((lo,hi,s));out.append((lo,hi,e,s));t=hi
    assert t==T
    return dict(endpoint=e,last_window=max(v for a,b,v in past if b>T-2*delay),slabs=out)

def fixture():
    z=replay(1,Q(5,2),[(0,1,0,0,0,1,0),(1,2,0,1,0,0,0),(2,Q(5,2),0,1,0,0,0)])
    assert z['endpoint']==3 and z['last_window']==3
    z=replay(1,3,[(0,1,0,0,0,0,0),(1,2,0,0,0,0,1),(2,3,0,0,0,0,0)])
    assert z['endpoint']==1
    print('PASS partial-slab and discontinuity error fixtures')
if __name__=='__main__':fixture()
