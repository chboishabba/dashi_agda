"""Exact rational charge-sharing and passive-loss certificate; not device data."""
from fractions import Fraction as Q
from random import Random

def energy(c,v): return c*v*v/2

def equalize(c1,c2,v1,v2):
    if c1<=0 or c2<=0: raise ValueError("capacitance must be positive")
    final=(c1*v1+c2*v2)/(c1+c2)
    initial=energy(c1,v1)+energy(c2,v2)
    final_energy=energy(c1,final)+energy(c2,final)
    lost=initial-final_energy
    formula=c1*c2*(v1-v2)**2/(2*(c1+c2))
    assert lost==formula
    assert c1*v1+c2*v2==(c1+c2)*final
    assert lost>=0
    return final,lost

def test():
    r=Random(36927)
    for _ in range(500):
        c1=Q(r.randint(1,1000),r.randint(1,1000))
        c2=Q(r.randint(1,1000),r.randint(1,1000))
        v1=Q(r.randint(-100,100),r.randint(1,17))
        v2=Q(r.randint(-100,100),r.randint(1,17))
        equalize(c1,c2,v1,v2)
    v,loss=equalize(Q(100,1000000),Q(100,1000000),Q(12),Q(0))
    assert v==6 and loss==Q(36,10000)
    return {"rational_cases":501,"reference_final_voltage":str(v),
            "reference_loss_joules":str(loss),"status":"passed"}

if __name__=="__main__":
    import json
    print(json.dumps(test(),indent=2))
