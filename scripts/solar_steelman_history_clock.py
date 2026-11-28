"""Exact period and block-error accounting in ambient max/history norm."""
from fractions import Fraction as Q

def atan_bounds(x,n):
    x=Q(x);assert 0<x<1 and n>0
    p=sum(((-1)**j*x**(2*j+1)/ (2*j+1) for j in range(n)),Q(0))
    z=p+(-1)**n*x**(2*n+1)/(2*n+1)
    return min(p,z),max(p,z)

def period_bounds(n=32):
    # Machin identity: pi=16 atan(1/5)-4 atan(1/239).
    a,b=atan_bounds(Q(1,5),n);c,d=atan_bounds(Q(1,239),n)
    return 32*a-8*d,32*b-8*c

def clock_error(T,dx,dh,n=32):
    """Derivative bounds must cover both endpoints and full shifted window."""
    T,dx,dh=map(Q,(T,dx,dh));assert min(dx,dh)>=0
    lo,hi=period_bounds(n)
    delta=max(abs(lo-T),abs(hi-T))
    return dict(delta=delta,state=delta*dx,history=delta*dh,
                bound=delta*max(dx,dh))

def aggregate(blocks,size):
    """Block row-sum error bounds add, NOT max; reject coverage gaps.
    Each record (start,stop,state,history) includes final readback errors.
    """
    cursor=0;x=h=Q(0)
    for lo,hi,e,f in sorted(blocks):
        e,f=Q(e),Q(f)
        assert lo==cursor and lo<hi<=size and min(e,f)>=0
        cursor=hi;x+=e;h+=f
    assert cursor==size
    return dict(state=x,history=h,bound=max(x,h))

def fixture():
    lo,hi=period_bounds()
    assert Q('6.283185307179586')<lo<hi<Q('6.283185307179587')
    assert clock_error(Q('6.283185307179586'),2,3)['bound']<Q(3,10**15)
    assert aggregate([(2,4,1,3),(0,2,2,1)],4)['bound']==4
    try:aggregate([(0,1,0,0),(2,4,0,0)],4)
    except AssertionError:pass
    else:raise AssertionError('gap accepted')
    print('PASS 4 exact clock and block coverage fixtures')
if __name__=='__main__':fixture()
