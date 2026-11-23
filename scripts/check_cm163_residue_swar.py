"""Bounded residue Kronecker lanes and deterministic CRT for CM slices."""
from math import isqrt
from time import perf_counter
import resource,json,argparse
from pathlib import Path
from sympy import Poly, ZZ, symbols
import check_cm163_fast as fast
import check_cm163_modular_diagonal as base
import check_cm163_derivative_slice as jet

def size_bound(a, shift):
    m=len(a)-1
    v=sum(abs(x) << (shift*(m-i)) for i,x in enumerate(a))
    return max(0,(v-1).bit_length()-shift*m)

def raw_inputs(p,K,J,diagonal):
    n=2*p if diagonal else p+1
    M=p*n
    if diagonal:
        h=[0]*(M+1)
        for i in range(n+1):h[p*i]+=J[i]
        for i in range(M-p+2):h[i+p-1]-=J[i]
        g=[0]*(n+1)
        for i in range(n-p+2):g[i+p-1]+=J[i]
        for i in range(3):g[i*p]-=J[i]
    else:
        h=J[:M+1];h[1]-=K
        g=[0]*(n+1);g[0]=1;g[p]=J[1]-K
    j=J[:n+1]
    return h,g,j,n

def construct_inputs(p,K,J,diagonal):
    h,g,j,n=raw_inputs(p,K,J,diagonal)
    t=1<<(p*n)
    assert 4*sum(abs(j[i])<<(p*(n-i)) for i in range(1,n+1))<=t
    assert 4*sum(i*abs(j[i])<<(p*(n-i)) for i in range(1,n+1))<=t
    # c_d=[q^(n-d)] Q J^-d (1-qJ'/J), Q=g*Norm(h).
    e=p*size_bound(h,1)+size_bound(g,p)+1+p*n
    return h,g,j,n,e

def mul(a,b,n,r):
    return [x%r for x in fast.mul(a,b,n)]

def normalized_product(p,inputs,r):
    h,g,j,n=inputs[:4]
    h=[x%r for x in h];g=[x%r for x in g];j=[x%r for x in j]
    N=len(h); inv=[1]
    while len(inv)<N:
        m=len(inv);k=min(2*m,N)
        v=mul(h[:k],inv,k-1,r)
        assert v[:m]==[1]+[0]*(m-1)
        inv+=mul(inv,[(-x)%r for x in v[m:]],k-m-1,r)
    assert mul(h,inv,N-1,r)==[1]+[0]*(N-1)
    d=[i*x%r for i,x in enumerate(h)]
    l=mul(d,inv,N-1,r)
    assert mul(h,l,N-1,r)==d
    norm=[1]
    for k in range(1,n+1):
        norm.append(sum(l[p*i]*norm[k-i] for i in range(1,k+1))*pow(k,-1,r)%r)
    return mul(g,norm,n,r),inv[:n+1]

def mod_slice(p,inputs,r):
    j,n=inputs[2:4]
    j=[x%r for x in j]
    rem,_=normalized_product(p,inputs,r)
    powers=[[1]+[0]*n]
    for k in range(n):powers.append(mul(powers[-1],j,n,r))
    coeff=[]
    for degree in range(n,-1,-1):
        c=rem[n-degree];coeff.append(c)
        for k in range(degree+1):rem[n-degree+k]=(rem[n-degree+k]-c*powers[degree][k])%r
    assert not any(rem)
    return coeff

def moduli(n,bits):
    for p in range(n+1,100000):
        if all(p%d for d in range(2,isqrt(p)+1)):
            r=p
            while r.bit_length()<bits:r*=p
            yield r

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--bits',type=int,default=768)
    ap.add_argument('--fast-j',action='store_true');ap.add_argument('--reference');ap.add_argument('--output');args=ap.parse_args()
    start=perf_counter();p=41;K=-640320**3
    if args.fast_j:
        from check_cm163_fast_j import j_unit
    else:
        j_unit=base.j_unit
    J=j_unit(2*p*p-p+1)
    inp=[construct_inputs(p,K,J,d) for d in (True,False)]
    bounds=[x[-1] for x in inp];print('certified coefficient height exponents',bounds,'J/setup seconds',perf_counter()-start,flush=True)
    acc=[[0]*(x[3]+1) for x in inp]; Q=1;count=0
    for r in moduli(2*p,args.bits):
        qi=pow(Q,-1,r)
        for i,x in enumerate(inp):
            if Q>2**(bounds[i]+1):continue
            residues=mod_slice(p,x,r)
            acc[i]=[a+Q*((v-a)*qi%r) for a,v in zip(acc[i],residues)]
            if Q*r>2**(bounds[i]+1):
                acc[i]=[a-Q*r if 2*a>Q*r else a for a in acc[i]]
                assert all(abs(a)<=2**bounds[i] for a in acc[i])
        Q*=r;count+=1
        print('CRT',count,'modulus bits',Q.bit_length(),'seconds',round(perf_counter()-start,3),flush=True)
        if Q>2**(max(bounds)+1):break
    assert Q>2**(max(bounds)+1)
    raw=json.dumps([[hex(c) for c in v] for v in acc],separators=(',',':')).encode('ascii')
    if args.reference:assert raw==Path(args.reference).read_bytes();print('PASS all 126 coefficient parity',flush=True)
    if args.output:Path(args.output).write_bytes(raw)
    polys=[Poly.from_list(a,symbols('X'),domain=ZZ) for a in acc]
    jet.main(lambda p:polys[0],lambda p,K:polys[1])
    print('PASS deterministic CRT bound',bounds,'packed operand bits',fast.peak,'calls',fast.calls,'RSS KiB',resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'seconds',perf_counter()-start,flush=True)

if __name__=='__main__':main()
