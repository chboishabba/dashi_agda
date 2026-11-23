"""Consumer-sufficient translated jets via formal residue substitution.
Masser's invariant: Masser (1975), via Bruinier–Ono–Sutherland
(arXiv:1301.5672, Lemma 2.3). Low-level nodal formula derived in Paper 9.
The modular correspondence and integral polynomial hypotheses are unchanged.
"""
from math import comb, isqrt
from fractions import Fraction
from pathlib import Path
from time import perf_counter
import argparse, json, resource
import check_cm163_fast as fast
from check_cm163_fast_j import j_unit
from check_cm163_residue_swar import raw_inputs, normalized_product, mul, moduli, mod_slice

CASES={3:-32768,5:-884736,11:-884736000,17:-147197952000,41:-640320**3}


def abs_sum(a, B, derivative=False):
    """Numerator and denominator of sum |a_i| B^-i (or its log derivative)."""
    num=0;den=1
    for i,x in enumerate(a):
        num=num*B+(i if derivative else 1)*abs(x)
        if i:den*=B
    return num,den


def ceil_log2_ratio(num, den):
    assert den>0 and num>=0
    if num<=den:return 0
    return ((num+den-1)//den-1).bit_length()


def jet_bounds(p,inputs,K,order):
    h,g,j,n=inputs[:4]
    v=j[:];v[1]-=K
    vv=v[:];vv[0]=0
    def admissible(B):
        C=B**p
        u,d=abs_sum(vv,C);t,e=abs_sum(v,C,True)
        return 4*u<=d and 4*t<=e
    lo,hi=1,2
    while not admissible(hi):lo,hi=hi,2*hi
    while hi-lo>1:
        mid=(lo+hi)//2
        if admissible(mid):hi=mid
        else:lo=mid
    B=hi;C=B**p
    H=ceil_log2_ratio(*abs_sum(h,B))
    A=ceil_log2_ratio(*abs_sum(g,C))
    # |V^-m|<=2^m, |1-qV'/V|<=2; Cauchy at q=1/C.
    bounds=[p*H+A+1+m+(C**(n-m)-1).bit_length() for m in range(order+1)]
    return B,bounds


def direct_jet(p,inputs,K,r,order=3,product=normalized_product):
    q,inv_h=product(p,inputs,r)
    j,n=inputs[2:4]
    v=[x%r for x in j];v[1]=(v[1]-K)%r
    # V=H for fixed slice; use its existing inverse when licensed.
    if inputs[0][:n+1]==[j[0],j[1]-K]+j[2:]:
        inverse=inv_h
    else:
        inverse=[1]
        for k in range(1,n+1):
            inverse.append(-sum(v[i]*inverse[k-i] for i in range(1,k+1))%r)
    assert mul(v,inverse,n,r)==[1]+[0]*n
    d=mul([i*x%r for i,x in enumerate(v)],inverse,n,r)
    d=[(1-d[0])%r]+[(-x)%r for x in d[1:]]
    z=mul(q,d,n,r)
    out=[]
    for m in range(order+1):
        out.append(z[n-m])
        if m<order:z=mul(z,inverse,n-m-1,r)
    return out


def translated_coeffs(coeff,K,order):
    n=len(coeff)-1
    return [sum(c*comb(n-i,m)*K**(n-i-m) for i,c in enumerate(coeff) if n-i>=m) for m in range(order+1)]


def construct(p,K,bits=384,order=3,ring_oracle=False,orbit=False):
    assert p>=3 and p%2 and all(p%d for d in range(2,isqrt(p)+1))
    assert bits>=1 and 0<=order<=p+1
    J=j_unit(2*p*p-p+1)
    inputs=[raw_inputs(p,K,J,d) for d in (True,False)]
    radius,bounds=zip(*(jet_bounds(p,x,K,order) for x in inputs))
    maxbound=max(map(max,bounds));Q=1;count=0
    acc=[[0]*(order+1) for x in inputs]
    if orbit:
        from check_cm_cyclic_orbit_norm import split_moduli, root, normalized_product as orbit_product
        rings=split_moduli(p,2*p,bits)
    else:
        rings=((None,r) for r in moduli(2*p,bits))
    for ell,r in rings:
        product=normalized_product
        if orbit:
            z=root(p,ell,r)
            product=lambda p,x,r: orbit_product(p,x,r,z)
        qi=pow(Q,-1,r)
        for i,x in enumerate(inputs):
            residues=direct_jet(p,x,K,r,order,product)
            if ring_oracle:
                expected=translated_coeffs(mod_slice(p,x,r),K,order)
                assert residues==[c%r for c in expected]
            acc[i]=[a+Q*((v-a)*qi%r) for a,v in zip(acc[i],residues)]
        Q*=r;count+=1
        if Q>2**(maxbound+1):break
    assert Q>2**(maxbound+1)
    acc=[[a-Q if 2*a>Q else a for a in row] for row in acc]
    assert all(abs(a)<=2**b for row,bs in zip(acc,bounds) for a,b in zip(row,bs))
    return acc,dict(radius_denominators=radius,bounds=bounds,crt_rings=count,crt_bits=Q.bit_length())


def cubic_gamma(rows):
    P,S=rows
    assert P[:2]==S[:2]==[0,0] and P[2] and S[2]
    return Fraction(2*S[3],S[2])-Fraction(P[3],P[2])

def masser_gamma(rows):
    P,S=rows
    assert P[0]==S[0]==0 and S[1] and P[1]==2*S[1]
    return Fraction(4*S[2]-P[2],S[1])

def family():
    expected={3:Fraction(32,77),5:Fraction(32,57),11:Fraction(640,903),17:Fraction(33440,43617)}
    for p in expected:
        K=CASES[p];t=perf_counter()
        rows,lower=construct(p,K,128,ring_oracle=True)
        gamma=cubic_gamma(rows);s2=4+Fraction(3*K,K-1728)+6*K*gamma
        assert s2==expected[p]
        tl=perf_counter()-t;t=perf_counter()
        rows,higher=construct(4*p-1,K,384,order=2)
        assert gamma==masser_gamma(rows)
        print(json.dumps(dict(p=p,masser_level=4*p-1,gamma=str(gamma),s2=str(s2),lower_seconds=tl,higher_seconds=perf_counter()-t,lower=lower,higher=higher)),flush=True)
    print("PASS four independently constructed cross-level comparisons",flush=True)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--p',type=int,default=41);ap.add_argument('--bits',type=int,default=384)
    ap.add_argument('--reference',type=Path);ap.add_argument('--ring-oracle',action='store_true');ap.add_argument('--output',type=Path)
    ap.add_argument('--orbit',action='store_true');ap.add_argument('--family',action='store_true');ap.add_argument('--compare-masser',action='store_true')
    args=ap.parse_args()
    if args.family:
        if args.orbit:ap.error('--orbit with --family is not supported; use individual --p runs')
        family();return
    p=args.p;K=CASES[p];start=perf_counter()
    rows,receipt=construct(p,K,args.bits,ring_oracle=args.ring_oracle,orbit=args.orbit)
    gamma=cubic_gamma(rows);s2=4+Fraction(3*K,K-1728)+6*K*gamma
    if args.reference:
        original=json.loads(args.reference.read_text())
        assert rows==[translated_coeffs([int(x,16) for x in row],K,3) for row in original]
        print('PASS all eight translated coefficients vs full slices',flush=True)
    if args.output:args.output.write_text(json.dumps([[hex(c) for c in row] for row in rows]))
    receipt.update(p=p,gamma=str(gamma),s2=str(s2),seconds=perf_counter()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,packed_calls=fast.calls,packed_operand_bits=fast.peak,reconstructed_slots=8)
    print(json.dumps(receipt),flush=True)
    if args.compare_masser:
        t=perf_counter();other,meta=construct(4*p-1,K,args.bits,order=2,orbit=args.orbit)
        assert gamma==masser_gamma(other)
        print(json.dumps(dict(masser_level=4*p-1,gamma=str(gamma),seconds=perf_counter()-t,**meta)),flush=True)

if __name__=='__main__':main()
