"""Weighted wall trace bound using same full-clock energy ledger, no new evolution."""
import json
from fractions import Fraction as Q
import numpy as np
from check_f8_local_dual_weld import I, exact_span
from run_f8_accumulated_interval import H,END,K,block
from check_f8_vector_interval import V,from_i

def trace_constant(b,s,k):
    # w0 |e0|² <= integral w(3/z |e|² - 2e e_y)
    # <= [3/(b k²)+1/(k sqrt(s))] B². Lift does not change e or e_y.
    return (b**3*(3/(b*k*k)+1/(k*s.sqrt()))).sqrt()

def run(receipt):
    x=json.load(open(receipt));assert x['cursor']==x['end']==END
    B=[I(Q(z)) for z in x['ledger'][1][0]];blocksize=x['identity']['block'];total=[[I(),I()] for _ in range(2)];maxtrace=[I(),I()]
    # final energy bound dominates all previous entire-slab upper bounds, since recurrence is nondecreasing.
    for i in range(0,END,blocksize):
        box,g,gt,rows=block(i,blocksize)
        if not rows:continue
        b=I(*box[0]);s=I(*box[2]);h=Q(H)*min(blocksize,END-i)
        for j,k in enumerate(K):
            C=trace_constant(b,s,k);maxtrace[j]=I(0,max(maxtrace[j].h,C.h))
            for r,(_,_,_,q) in enumerate(rows):
                m=Q(float(q.mag()[j]));total[r][j]+=I(0,h*B[j].h*C.h*m)
    # independent global window L1 bound from the existing F8 tail ledger:
    # ||a2''-a1'||_1<=2700, ||a0||_1<=1/2; b<=1/8 and s>=64/65.
    # trace bound squared =3 b²/k²+b³/(k sqrt(s)), monotone in b.
    fallback=[]
    for j,k in enumerate(K):
        b=I(Q(1,8));s=I(Q(64,65));C=trace_constant(b,s,k)
        fallback.append((B[j]*C*(2700+k*k/2)).h)
    return dict(local_radii=[[float(z.h) for z in row] for row in total],global_radii=[float(z) for z in fallback],max_trace=[float(z.h) for z in maxtrace],scope='conditional scalar modal wall-trace bound, no TT or omitted tail')

if __name__=='__main__':
    import sys;print(json.dumps(run(sys.argv[1]),indent=2))
