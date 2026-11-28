#!/usr/bin/env python3
"""Independent exact reader of production postorder trace, matching Lean Trace.
No GMP Boolean or output hash supplies the division witnesses.
"""
import argparse, hashlib, sys
from fractions import Fraction as F
from check_pi_geometry_closure import leaf,join,floor_gate

def check(path):
    stack=[];receipt=None;merges=0
    with open(path) as f:
        for line in f:
            if receipt is not None: raise ValueError("trailing trace records")
            tag,*fields=line.split()
            if tag=="empty" and not fields: stack.append(((1,1,0),None,None,0))
            elif tag=="leaf" and len(fields)==1:
                i=int(fields[0]);assert i>=0
                stack.append((leaf(i),i,i+1,1))
            elif tag=="merge" and len(fields)==3:
                g,rq,lp=map(int,fields)
                r,ra,rb,rn=stack.pop();l,la,lb,ln=stack.pop()
                assert g>0 and rq>0 and l[0]==g*lp and r[1]==g*rq
                assert not (ln and rn) or lb==ra
                stack.append((join((lp,l[1],l[2]),(r[0],rq,r[2])),la if ln else ra,rb if rn else lb,ln+rn))
                merges+=1
            elif tag=="receipt" and len(fields)==5: receipt=tuple(map(int,fields))
            else: raise ValueError("bad trace record")
    assert receipt is not None and len(stack)==1
    d,n,r,s,x=receipt
    (p,q,t),a,b,count=stack.pop()
    assert d>=1 and n>=1 and s>0 and r>=0 and (a,b,count)==(0,n,n)
    assert r*r<=10005*s*s<(r+1)**2
    P,Q,T=leaf(n)
    lo,hi=sorted((F(t,q),F(t*Q+p*T,q*Q)))
    assert lo>0
    assert floor_gate(F(426880*r,s)/hi,F(426880*(r+1),s)/lo,d)==x
    return d,n,merges,hashlib.sha256(str(x).encode()).hexdigest()

if __name__=="__main__":
    sys.set_int_max_str_digits(0)
    if not __debug__: raise RuntimeError("assertions required")
    ap=argparse.ArgumentParser();ap.add_argument("trace");a=ap.parse_args()
    print("PASS production trace",*check(a.trace))
