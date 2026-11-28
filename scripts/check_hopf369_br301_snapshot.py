"""BR301: exact binary-rational snapshot binding of the actual BR240 history.
The selected coordinates are a metric observation, NOT the BR145 tidal
observable. Keep that distinction and do not claim native kernel acceptance.
"""
from fractions import Fraction as F
import hashlib
import json
import numpy as np
from check_hopf369_br240_metric_history import run

def rat(x):
    return F.from_float(float(x))
def wire(x):
    return [x.numerator,x.denominator]
def main():
    gs,dx=run(11,full=True)
    rows=[]
    for k,(a,b) in enumerate(zip(gs,gs[1:])):
        p=(5,5,5)
        q,e=rat(a[p][4,4]),rat(a[p][3,4])
        q1,e1=rat(b[p][4,4]),rat(b[p][3,4])
        dq,de=q1-q,e1-e
        # Reflection in the fifth coordinate leaves diagonal, negates mixed.
        left=(q+dq,-e+de)
        right=(q+dq,-(e+de))
        assert left[0]==right[0] and left[1]-right[1]==2*de
        assert (q+dq,e+de)==(q1,e1)
        row=dict(history=k,time=k+1,depth=11,iteration=0,version=1,
                 before=list(map(wire,(q,e))),after=list(map(wire,(q1,e1))),
                 increments=list(map(wire,(dq,de))),signed_residual=wire(2*de),
                 source_before=hashlib.sha256(a.tobytes()).hexdigest(),
                 source_after=hashlib.sha256(b.tobytes()).hexdigest())
        rows.append(row)
    print(json.dumps(dict(observation='metric g44,g34 at centre, not normalized tidal T34',rows=rows),sort_keys=True))
if __name__=='__main__':main()
