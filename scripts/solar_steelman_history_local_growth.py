"""Local comparison envelope for arbitrary unit continuous ratio histories.
Uses actual coefficient balls, no trajectory-specific initial interpolation.
"""
import sympy as S
from solar_steelman_history_clock import period_bounds
from solar_steelman_history_defect_replay import replay
from solar_steelman_history_polynomial_defect import bernstein_bound,logarithmic_norm
from solar_steelman_history_harmonic_enclosure import s

def envelope(slabs,delay,T,window_start,r,rprime):
    delay,T,window_start,r,rprime=map(S.Rational,(delay,T,window_start,r,rprime))
    assert 0<delay and 2*delay<window_start<T and min(r,rprime)>=0
    # slabs contain exact raw coefficient norm bounds, with signed mu.
    rows=[]
    for lo,hi,mu,a,b,c in slabs:
        assert min(a,b,c)>=0
        rows.append((lo,hi,mu,b*max(1,r),c*max(1,r),0,0))
    z=replay(delay,T,rows,1,(1,1))
    G=max([S.Integer(1)]+[S.Rational(v[3]) for v in z['slabs']])
    # For derivative and clock bounds use full-horizon G (safe fallback).
    D=max(a*G+(b+c)*max(1,r)*G for _,_,_,a,b,c in slabs)
    H=rprime*G+r*D
    W=max(S.Rational(v[3]) for v in z['slabs'] if v[1]>window_start)
    return dict(g=max(1,r)*W,dx=D,dh=H,horizon=T,window_start=window_start,global_growth=G)

def construct(m,a,delay,trace_T,degree=8):
    from solar_steelman_history_matrix_enclosure import construct as matrix
    from solar_steelman_history_exact_bounds import ratio_bounds
    delay,trace_T=map(S.Rational,(delay,trace_T))
    plo,phi=map(S.Rational,period_bounds())
    T=max(phi,trace_T);window=min(plo,trace_T)-2*delay
    rr=[ratio_bounds(c) for _,_,c in a['models']]
    r=max(v[1] for v in rr);rp=max(v[2] for v in rr)
    slabs=[];lo=S.Integer(0)
    while lo<T:
        hi=min(lo+delay,T)
        (A,ea),(B,eb),(C,ec),_=matrix(m,a,lo,hi,degree)
        norm=lambda M,e:bernstein_bound(M,s)+e
        slabs.append((lo,hi,logarithmic_norm(A,s,ea),norm(A,ea),norm(B,eb),norm(C,ec)))
        lo=hi
    z=envelope(slabs,delay,T,window,r,rp)
    z.update(slabs=slabs,r=r,rprime=rp,delay=delay,trace_T=trace_T)
    return z

def fixture():
    # zero dynamics with arbitrary initial history, no delayed forcing.
    z=envelope([(i,i+1,0,0,0,0) for i in range(6)],1,6,3,1,0)
    assert z['g']==1 and z['dx']==0 and z['dh']==0
    z=envelope([(i,i+1,-1,1,0,0) for i in range(6)],1,6,3,1,0)
    assert z['g']==S.Rational(1,8)
    print('PASS local growth envelope controls')
if __name__=='__main__':fixture()
