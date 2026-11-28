"""Joint causal-budget tiles; exact absolute E4/SMS bound.
Uses same localized characteristic lift, radial integrations and original readout.
"""
from fractions import Fraction as Q
from math import factorial,comb
from functools import lru_cache
import json,sys,time
from check_f8_cap_localized_energy import run as baseline

e=Q(2718,1000);eps=Q(1,25);pulse=Q(13,200);rho=Q(361,10**6)
@lru_cache(None)
def ex(n):return e**(-min(int(n),1000))

def bump(X):
    assert X>10
    return ex(X-1)

def radial(H,width):
    # Cauchy radius delta/16; real part of the reciprocal >=16/(17 delta).
    X=eps*Q(8,17)/H;assert X>9
    D=[Q(factorial(j))*(16/H)**j*bump(X) for j in range(10)]
    C=[sum((Q(comb(j,i))*D[i]*(20/width)**(j-i) for i in range(j+1)),Q(0)) for j in (8,9)]
    return eps**4*H*(eps*C[1]+9*C[0])

def source(smax,length,width):
    X=pulse/(4*smax);a=bump(X)
    # Difference of two shifted smooth cumulative cutoffs, each one box + mollifier.
    A=24*a;At=96*a+24*(4/pulse*X**2+8/width)*a
    return 16*1200*length*2*(7*A+At)

def receiver(dmax,length):
    X=Q(1,20)/dmax;a=15*bump(X)
    return length*(Q(33,2)+160*X**2+100*(2*X**2+8*X**3+4*X**4))*a

def run(n):
    assert n in (8,16,32,64,128)
    start=time.monotonic();smax=Q(9,20000);dmax=Q(7,20000);h=smax/n;g=dmax/n;width=min(h,g)/4
    # Common translated convolution of Heaviside; C_j=1 at/below jh,
    # C_j=0 at/above jh+width. phi_j=C_j-C_(j-1), phi_1=C_1 on s>=0.
    # Sum phi_j=C_n=1 throughout causal emission cap; no source change there.
    vals=[];scale=10**300;total=0;skipped=0;largest=(0,None)
    for i in range(n):
        d0=i*g;W=receiver(d0+g,g)
        for j in range(n):
            s0=j*h;allow=rho-Q(7,10)*s0-Q(99,100)*d0
            if allow<=0:skipped+=1;continue
            H=allow+width
            # Radial cutoff is one for depth <=allow, zero at depth >=H.
            # Only this source tile can reach this receiver tile, by joint cap.
            bound=2*radial(H,width)*source((j+1)*h+width,h+width,width)*W
            v=(bound.numerator*scale+bound.denominator-1)//bound.denominator
            total+=v
            if v>largest[0]:largest=(v,[i,j])
            vals.append(v)
    # All additions exact with per-tile ceiling at 1e-300.
    z=Q(total,scale);p=0
    while z<Q(1,10**(p+1)):p+=1
    return dict(n=n,tiles=len(vals),empty_tiles=skipped,source_step=str(h),receiver_step=str(g),cutoff_width=str(width),bound_upper=float(z),decimal_upper='1e-'+str(p),exact_ceiling_numerator=str(total),exact_ceiling_denominator='1e300',largest_tile=largest[1],largest_tile_upper=float(Q(largest[0],scale)),seconds=time.monotonic()-start,scope='conditional absolute fixed-window scalar TT yy E4/SMS bound; no sign, no new trajectory or physical promotion')
if __name__=='__main__':
    b=baseline();print(json.dumps(dict(baseline=b['decimal_upper'],**run(int(sys.argv[1]))),indent=2))
