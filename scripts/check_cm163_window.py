"""Exact support-window Newton inversion using the existing GMP backend."""
import random
import resource
import check_cm163_fast as fast
import check_cm163_modular_diagonal as base
import check_cm163_derivative_slice as jet


def window(a,b,lo,hi,block=256):
    assert 0<=lo<=hi and block>0
    out=[0]*(hi-lo)
    for i in range(0,min(len(a),hi),block):
        u=a[i:i+block]
        if not any(u):continue
        for j in range(0,min(len(b),hi-i),block):
            v=b[j:j+block]
            end=len(u)+len(v)-1
            left=max(0,lo-i-j);right=min(end,hi-i-j)
            if left>=right or not any(v):continue
            if right<=end-left:
                c=fast.mul(u,v,right-1)[left:right]
            else:
                c=fast.mul(u[::-1],v[::-1],end-left-1)[end-right:end-left][::-1]
            for k,x in enumerate(c,i+j+left-lo):out[k]+=x
    return out


def logder(h):
    assert h[0]==1
    n=len(h);g=[1]
    while len(g)<n:
        m=len(g);k=min(2*m,n)
        r=[-x for x in window(h[:k],g,m,k)]
        g+=window(g,r,0,k-m)
    assert window(h,g,0,n)==[1]+[0]*(n-1)
    d=[i*x for i,x in enumerate(h)]
    l=window(d,g,0,n)
    assert window(h,l,0,n)==d
    return l


def main():
    rng=random.Random(41)
    for _ in range(128):
        a=[rng.randrange(-100,101) for _ in range(rng.randrange(1,40))]
        b=[rng.randrange(-100,101) for _ in range(rng.randrange(1,40))]
        lo=rng.randrange(len(a)+len(b));hi=rng.randrange(lo,len(a)+len(b)+5)
        assert window(a,b,lo,hi,7)==(base.convolution(a,b,hi-1)[lo:hi] if hi else [])
        h=[1]+a
        assert logder(h)==fast.logder(h)
    for p in (3,5,7,11):
        assert base.diagonal(p,logder)==base.diagonal(p)
        assert jet.slice_poly(p,-640320**3,logder)==jet.slice_poly(p,-640320**3)
    print('128 window/inverse comparisons and 8 complete small-prime comparisons PASS',flush=True)
    fast.peak=fast.calls=0
    jet.main(lambda p:base.diagonal(p,logder),lambda p,K:jet.slice_poly(p,K,logder))
    print('max packed operand bits',fast.peak,'multiplications',fast.calls,'peak RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)

if __name__=='__main__':main()
