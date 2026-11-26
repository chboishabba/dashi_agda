"""Exact original fixed-window causal node/time-stage support ledger.
Conditional on continuum finite propagation; no discrete RK causality claim.
Floating clock estimates only propose brackets, all decisions rational.
"""
from fractions import Fraction as Q
from math import isqrt, asinh, sqrt, floor, ceil
from functools import lru_cache
import json
from scipy.optimize import brentq
from check_f8_global_wall_kernel import Fbox

EPS=Q(1,25)
RHO=Q(361,10**6)
S_MAX=Q(9,20000)
D_MAX=Q(7,20000)


def root(x):
    assert x>=0
    d=10**18;n=isqrt((x*d*d).numerator//(x*d*d).denominator)
    return Q(n,d),Q(n+1,d)


def clock_box(T):
    # F is strictly decreasing in b; bracket the whole rational time interval.
    mid=float(sum(T)/2)
    b=brentq(lambda b:asinh(1/b)-sqrt(1+b*b)-mid,.07,1.01,xtol=1e-15)
    den=10**12
    lo=Q(floor(b*den)-3,den);hi=Q(ceil(b*den)+3,den)
    assert Fbox(lo)[0]>T[1] and Fbox(hi)[1]<T[0],(T,lo,hi)
    return lo,hi


def mul_positive(a,k):
    assert k>=0
    return a[0]*k,a[1]*k


def gap(s,t,bs,bt,r):
    # Maximum attainable radial distance from any point on a source sphere.
    lag=(t[0]-s[1],t[1]-s[0]);dz=(bs[0]-bt[1],bs[1]-bt[0])
    assert lag[0]>0 and dz[0]>0
    return lag[0]**2-dz[1]**2-r[1]**2,lag[1]**2-dz[0]**2-r[0]**2


def compact_box(g):
    D=10**18
    return [str(Q(floor(g[0]*D),D)),str(Q(ceil(g[1]*D),D))]

def label(g):return 'dark' if g[1]<0 else 'open' if g[0]>0 else 'undecided'


def main():
    f=Fbox(Q(1));l=Fbox(Q(1,12));span=(l[0]-f[1],l[1]-f[0]);end=(span[0]-Q(1,20),span[1]-Q(1,20));r=(root(span[0]**2-Q(11,12)**2)[0]-Q(3,250),root(span[1]**2-Q(11,12)**2)[1]-Q(3,250));be=clock_box((l[0]-Q(1,20),l[1]-Q(1,20)))
    reach=(root(end[0]**2-(1-be[0])**2)[0],root(end[1]**2-(1-be[1])**2)[1]);cut=(r[0]-reach[1],r[1]-reach[0]);assert EPS-RHO<cut[0]<cut[1]<EPS
    # Same monotonicity proof as fixed_window_causal_cap: D decreases with
    # emission time and increases with reception time, as |b'|<1.
    rows=[]
    for n in (2258,4516,6347,7225,14450,28900,57800):
        h=mul_positive(span,Q(1,n));j=n-ceil(Q(1,20)/h[0]);assert j*h[1]<end[0] and (j+1)*h[0]>end[1]
        s=h[0]/2,h[1]/2;t=mul_positive(h,Q(j));bs=clock_box((f[0]+s[0],f[1]+s[1]));bt=clock_box((f[0]+t[0],f[1]+t[1]));g=gap(s,t,bs,bt,(r[0]-EPS,r[1]-EPS))
        assert label(g)!='undecided'
        # Check all potentially causal half-stage times / base sample times
        # within the prior physical support cap; all other pairs excluded.
        ks=[k for k in range(1,int(2*S_MAX/h[0])+1)]
        js=[i for i in range(j,max(-1,j-int(D_MAX/h[0])-3),-1) if i*h[1]>=end[0]-D_MAX]
        clocks={};counts={'dark':0,'open':0,'undecided':0}
        for k in ks:
            ss=mul_positive(h,Q(k,2));clocks[k]=clock_box((f[0]+ss[0],f[1]+ss[1]))
        for i in js:
            tt=mul_positive(h,Q(i));bi=clock_box((f[0]+tt[0],f[1]+tt[1]))
            for k in ks:
                gg=gap(mul_positive(h,Q(k,2)),tt,clocks[k],bi,(r[0]-EPS,r[1]-EPS));counts[label(gg)]+=1
        assert counts['undecided']==0
        if label(g)=='dark':assert counts['open']==0
        lag=(t[0]-s[1],t[1]-s[0]);dz=(bs[0]-bt[1],bs[1]-bt[0]);D=(root(lag[0]**2-dz[1]**2)[0],root(lag[1]**2-dz[0]**2)[1]);samplecut=(r[0]-D[1],r[1]-D[0]);nodes={}
        for dr in (Q(1,125),Q(3,500)):
            x=[i*dr for i in range(ceil(EPS/dr)+1)]
            assert all(z<cut[0] or z>cut[1] for z in x)
            assert all(z<samplecut[0] or z>samplecut[1] for z in x)
            nodes[str(dr)]=dict(nodes=[str(z) for z in x],continuum_dark=[i for i,z in enumerate(x) if z<cut[0]],sampled_dark=[i for i,z in enumerate(x) if z<samplecut[0]])
        rows.append(dict(n=n,dt=[float(x) for x in h],last_window_node=j,earliest_stage_elapsed=[float(x) for x in s],last_sample_to_end=[float(end[0]-t[1]),float(end[1]-t[0])],max_gap=compact_box(g),max_gap_display=[float(x) for x in g],original_support=label(g),cap_pair_counts=counts,sampled_radial_cut=compact_box(samplecut),sampled_radial_cut_display=[float(x) for x in samplecut],nodes=nodes))
    assert all(x['original_support']=='dark' for x in rows[:4]) and all(x['original_support']=='open' for x in rows[4:])
    print(json.dumps(dict(scope='continuum causal support for true original spatial support and sampled stage/observer times; no discrete propagation or sign claim',continuum_radial_cut=compact_box(cut),continuum_radial_cut_display=[float(x) for x in cut],rows=rows),indent=2))

if __name__=='__main__':main()
