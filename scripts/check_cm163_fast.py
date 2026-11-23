"""Exact signed packed multiplication and Newton inversion for CM slices."""
import ctypes as c
from ctypes.util import find_library
from time import perf_counter
import random
import resource
import check_cm163_modular_diagonal as base
import check_cm163_derivative_slice as jet

lib=c.CDLL(find_library('gmp'))
class Z(c.Structure):
    _fields_=[('alloc',c.c_int),('size',c.c_int),('limbs',c.c_void_p)]
for name,args in [('init',[c.POINTER(Z)]),('clear',[c.POINTER(Z)]),('mul',[c.POINTER(Z)]*3),('import',[c.POINTER(Z),c.c_size_t,c.c_int,c.c_size_t,c.c_int,c.c_size_t,c.c_void_p]),('export',[c.c_void_p,c.POINTER(c.c_size_t),c.c_int,c.c_size_t,c.c_int,c.c_size_t,c.POINTER(Z)])]:
    f=getattr(lib,'__gmpz_'+name); f.argtypes=args; f.restype=c.c_void_p if name=='export' else None
peak=0
calls=0

def mul(a,b,n):
    global peak,calls
    calls+=1
    a=a[:n+1]; b=b[:n+1]
    w=(max(map(abs,a)).bit_length()+max(map(abs,b)).bit_length()+min(len(a),len(b)).bit_length()+2+7)//8
    R=1<<(8*w)
    def pack(v):
        carry=0; out=bytearray()
        for x in v:
            carry,d=divmod(x+carry,R);out.extend(d.to_bytes(w,'little'))
        return int.from_bytes(out,'little')+(carry<<(8*w*len(v)))
    A,B=pack(a),pack(b)
    peak=max(peak,abs(A).bit_length(),abs(B).bit_length())
    x,y,z=Z(),Z(),Z()
    for v in (x,y,z):lib.__gmpz_init(c.byref(v))
    try:
        for v,i in ((x,A),(y,B)):
            raw=abs(i).to_bytes((abs(i).bit_length()+7)//8,'little')
            lib.__gmpz_import(c.byref(v),len(raw),-1,1,0,0,raw)
        lib.__gmpz_mul(c.byref(z),c.byref(x),c.byref(y))
        buf=c.create_string_buffer((abs(A).bit_length()+abs(B).bit_length()+7)//8+1); count=c.c_size_t()
        lib.__gmpz_export(buf,c.byref(count),-1,1,0,0,c.byref(z))
        prod=int.from_bytes(buf.raw[:count.value],'little')
        if (A<0)!=(B<0):prod=-prod
        size=w*(n+1); raw=(prod & ((1<<(8*size))-1)).to_bytes(size,'little')
        out=[];carry=0
        for i in range(n+1):
            d=int.from_bytes(raw[i*w:(i+1)*w],'little')+carry
            carry=(d+R//2)//R;out.append(d-carry*R)
        return out
    finally:
        for v in (x,y,z):lib.__gmpz_clear(c.byref(v))

def logder(h):
    n=len(h)-1;g=[1]
    assert h[0]==1
    while len(g)<len(h):
        k=min(2*len(g),len(h))-1
        e=mul(h,g,k);e=[2-e[0]]+[-x for x in e[1:]]
        g=mul(g,e,k)
    assert mul(h,g,n)==[1]+[0]*n
    d=[i*x for i,x in enumerate(h)];l=mul(d,g,n)
    assert mul(h,l,n)==d
    return l

if __name__=='__main__':
    rng=random.Random(41)
    for n in range(1,65):
        a=[rng.randrange(-100,101) for _ in range(n)];b=[rng.randrange(-100,101) for _ in range(n)]
        assert mul(a,b,n)==base.convolution(a,b,n)
        h=[1]+a;l=logder(h);r=[0]
        for k in range(1,len(h)):r.append(k*h[k]-sum(h[i]*r[k-i] for i in range(1,k)))
        assert l==r
    print('64 signed products and 64 inverse/log derivative regressions PASS',flush=True)
    # Same reconstruction consumers, with scalar default preserved.
    for p in (3,5,7,11):
        assert base.diagonal(p,logder)==base.diagonal(p)
        assert jet.slice_poly(p,-640320**3,logder)==jet.slice_poly(p,-640320**3)
    print('8 full polynomial parity cases PASS',flush=True)
    jet.main(lambda p:base.diagonal(p,logder),lambda p,K:jet.slice_poly(p,K,logder))
    print('max packed operand bits',peak,'multiplications',calls,'peak RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
