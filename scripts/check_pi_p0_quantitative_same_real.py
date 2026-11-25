#!/usr/bin/env python3
"""Fixed-schedule rational same-real certificate fixtures (UNEXECUTED).
All-degree proof is in Paper9BishopQuantitativeEndpoint20261125.md.
Finite overlap checks are regression only, not an analytic or kernel theorem.
"""
import argparse
from fractions import Fraction as F
from check_chudnovsky_exact import interval, A, B, C
from check_chudnovsky_bishop_semantics import atan_bracket

def require(ok, label):
    if not ok:
        raise AssertionError(label)

def constants():
    require(42*1728*(1<<41)<C, "uniform term contraction")
    require(A+B<42*A, "weighted ratio")
    require(2*426880<A, "root-width coefficient")
    require(4*426880*101<16*A, "tail-width coefficient")
    require(F(16,5)+F(4,239)<4, "Machin width coefficient")
    # Exact uniform cusp-to-CM real q segment majorants.
    r=F(1,1<<36)
    require(240*r/(1-16*r)<F(1,16),"E4 uniform majorant")
    require(504*r/(1-64*r)<F(1,16),"E6 uniform majorant")
    require(F(17,16)**2<2*F(15,16)**3,"z inside unit disk")
    require(144*B*B==163*(C+1728),"period constant")
    require((1-F(77265280,90856689))/6==F(A,B),"CM coefficient ratio")

def schedules(k):
    require(k>=0,"nonnegative bit precision")
    return max(1,(k+45)//41),k+2

def machin_partial_and_interval(k):
    if k==0:
        return F(0),-F(4,239),F(16,5)
    a,b=atan_bracket(5,k)
    c,d=atan_bracket(239,k)
    # Alternation: original k-term sum is upper for odd k, lower for even.
    partial=16*(b if k%2 else a)-4*(d if k%2 else c)
    return partial,16*a-4*d,16*b-4*c

def witness(k):
    n,bits=schedules(k)
    lo,hi=interval(n,bits)
    partial,ml,mh=machin_partial_and_interval(k)
    midpoint=(lo+hi)/2
    require(hi-lo<F(1,1<<k),"fixed CH width")
    require(mh-ml<4*F(1,25**k),"fixed Machin width")
    require(ml<=partial<=mh,"literal Machin partial")
    require(max(lo,ml)<=min(hi,mh),"finite overlap (not proof for all k)")
    require(abs(midpoint-partial)<=F(4,k+1),"native error fixture")
    return n,bits

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--bits",nargs="+",type=int,default=[0,1,2,35,36,37,40,41,42,63,64,65,128,256,512,1024])
    args=parser.parse_args()
    constants()
    for k in args.bits:
        n,b=witness(k)
        print(f"k={k} cutoff={n} root_bits={b} PASS")
if __name__=="__main__":
    main()
