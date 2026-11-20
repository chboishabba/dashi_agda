"""Cyclic orbit doubling over split prime-power rings (classical norm)."""
from math import isqrt
from time import perf_counter

def split_moduli(p,n,bits):
    for ell in range(p+1,1000000,p):
        if ell<=n or any(ell%d==0 for d in range(2,isqrt(ell)+1)):
            continue
        r=ell
        while r.bit_length()<bits:r*=ell
        yield ell,r

def root(p,ell,r):
    # p prime; exponentiation projects onto the order-p subgroup.
    phi=r-r//ell
    assert phi%p==0
    for a in range(2,ell):
        z=pow(a,phi//p,r)
        if z%ell!=1 and pow(z,p,r)==1:
            return z
    raise ValueError("no split root")

def cyclic_norm(h,p,n,r,z,mul):
    assert h[0]%r==1 and pow(z,p,r)==1
    from math import gcd
    assert gcd(p,r)==1 and all(gcd(pow(z,k,r)-1,r)==1 for k in range(1,p))
    M=p*n
    h=([x%r for x in h]+[0]*(M+1))[:M+1]
    phases=[pow(z,k,r) for k in range(p)]
    def shift(a,k):
        return [x*phases[(i*k)%p]%r for i,x in enumerate(a)]
    def product(a,b):
        return mul(a,b,M,r)
    out=h; length=1
    for bit in bin(p)[3:]:
        out=product(out,shift(out,length))
        length*=2
        if bit=="1":
            out=product(out,shift(h,length))
            length+=1
    assert length==p and out[0]==1
    assert not any(x for i,x in enumerate(out) if i%p)
    return out[::p]

def diagonal_valuation_norm(h,j,p,n,r,mul):
    """Projected formal log; denominators must be units, no split root needed."""
    from math import gcd
    M=p*n
    v=p-1
    top=M//v
    if any(gcd(k,r)!=1 for k in range(1,max(n,top)+1)):
        raise ValueError("valuation log requires unit denominators")
    A=[x%r for x in j[:n+1]]
    assert A[0]==1
    lifted=[0]*(M+1)
    for i,a in enumerate(A):lifted[p*i]=a
    # Recover B from the actual source H, not a substitute J producer.
    assert all((lifted[i]-h[i])%r==0 for i in range(v))
    B=[(lifted[i]-h[i])%r for i in range(v,M+1)]
    assert B[0]==1
    inv=[1]
    for k in range(1,n+1):
        inv.append(-sum(A[i]*inv[k-i] for i in range(1,k+1))%r)
    log=[0]*(n+1)
    power=[1]; ip=[1]
    for k in range(1,top+1):
        degree=M-k*v
        power=mul(power,B,degree,r)
        offset=(k*v+p-1)//p
        precision=n-offset
        ip=mul(ip,inv,precision,r)
        projected=power[offset*p-k*v::p]
        term=mul(projected,ip,precision,r)
        scale=-p*pow(k,-1,r)%r
        for i,a in enumerate(term):log[offset+i]=(log[offset+i]+scale*a)%r
    exp=[1]
    for k in range(1,n+1):
        exp.append(sum(i*log[i]*exp[k-i] for i in range(1,k+1))*pow(k,-1,r)%r)
    ap=[1]; base=A; e=p
    while e:
        if e&1:ap=mul(ap,base,n,r)
        e//=2
        if e:base=mul(base,base,n,r)
    return mul(ap,exp,n,r)

def normalized_product(p,inputs,r,z):
    from check_cm163_residue_swar import mul
    h,g,j,n=inputs[:4]
    norm=cyclic_norm(h,p,n,r,z,mul)
    # Original direct-jet consumer expects short H inverse, not full inverse.
    inv=[1]
    for k in range(1,n+1):
        inv.append(-sum(h[i]*inv[k-i] for i in range(1,k+1))%r)
    return mul([x%r for x in g],norm,n,r),inv

def main():
    from check_cm163_residue_swar import raw_inputs, normalized_product as oracle
    from check_cm163_fast_j import j_unit
    from check_cm_direct_jet import CASES
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--levels',nargs='+',type=int,default=[3,5,11,17,41])
    ap.add_argument('--bits',type=int,default=128)
    ap.add_argument('--rings',type=int,default=2)
    args=ap.parse_args()
    from itertools import islice
    count=0
    for p in args.levels:
        J=j_unit(2*p*p-p+1)
        for ell,r in islice(split_moduli(p,2*p,args.bits),args.rings):
            z=root(p,ell,r)
            for diagonal in (True,False):
                inputs=raw_inputs(p,CASES[p],J,diagonal)
                t=perf_counter();a=normalized_product(p,inputs,r,z);dt=perf_counter()-t
                t=perf_counter();b=oracle(p,inputs,r);ot=perf_counter()-t
                assert a==b
                if diagonal:
                    from math import gcd
                    from check_cm163_residue_swar import mul
                    h,g,j,n=inputs[:4]
                    if all(gcd(k,r)==1 for k in range(1,max(n,p*n//(p-1))+1)):
                        vn=diagonal_valuation_norm(h,j,p,n,r,mul)
                        assert mul([x%r for x in g],vn,n,r)==b[0]
                count+=1
                print(p,ell,diagonal,dt,ot,flush=True)
    print('PASS original normalized product and short inverse',count)

if __name__=='__main__':main()
