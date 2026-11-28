#!/usr/bin/env python3
"""Independent integer replay of the original GMP receipt; optionally emit Lean source.

The replay does not certify the analytic Chudnovsky identity. The generated
Lean theorem uses the original literal prefix and the companion's floorFromRaw.
No kernel or compiler is invoked here.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

A, B, C = 13591409, 545140134, 640320**3

def require(ok, name):
    if not ok:
        raise ValueError(name)

def atom(n):
    p = -24*(2*n-1)*(6*n-5)*(6*n-1) if n else 1
    q = C*n**3 if n else 1
    return p, q, p*(A+B*n)

def split(a,b):
    if a==b:
        return 1,1,0
    if b-a==1:
        return atom(a)
    m=(a+b)//2
    p,q,t=split(a,m)
    P,Q,T=split(m,b)
    return p*P,q*Q,t*Q+p*T

def replay(doc):
    require(doc["schema"]=="paper9-gmp-window-v1","schema")
    require(doc["mode"] in ("plain","cross"),"mode")
    d,n,bits=map(doc.__getitem__,("digits","n","bits"))
    require(all(type(v) is int for v in (d,n,bits)) and d>=0 and n>=1 and bits>=1,"indices")
    get=lambda k:int(doc[k],16)
    p,q,t=(get(k) for k in ("p","q","t"))
    P,Q,T=split(0,n)
    require(q>0 and Q>0 and p*Q==P*q and t*Q==T*q,"literal prefix ratio")
    a,b,c=atom(n)
    nt,nq=t*b+p*c,q*b
    require(nt==get("next_t") and nq==get("next_q"),"adjacent step")
    require(t>0 and nt>0,"positive prefixes")
    r,s=get("root"),get("scale")
    require(s==1<<bits and r>=0 and r*r<=10005*s*s<(r+1)**2,"sqrt witness")
    lo,ld,hi,hd=t,q,nt,nq
    if hi*ld<lo*hd:
        lo,ld,hi,hd=hi,hd,lo,ld
    ln,lq,un,uq=426880*r*hd,s*hi,426880*(r+1)*ld,s*lo
    require((ln,lq,un,uq)==tuple(get(k) for k in
        ("lower_num","lower_den","upper_num","upper_den")),"window corners")
    x=get("floor")
    scale=10**d
    lower=scale*ln-x*lq
    upper=(x+1)*uq-scale*un
    require(ln*uq<=un*lq and 0<=lower<lq and upper>0,"floor residual")
    require(lower==get("lower_residual") and upper==get("upper_residual"),"literal residuals")
    require(hashlib.sha256(str(x).encode()).hexdigest()==doc["sha256"],"digit digest")
    return n,r,s,d,x

def lean_source(n,r,s,d,x):
    # Deliberately use kernel decision proofs, not a native or external
    # assertion. Large receipts may exceed the local reduction budget.
    return f"""import Integration.Paper9GMPWindowAcceptance

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Integration.Paper9GMPWindowAcceptance

theorem receiptFloor : ⌊(10:ℝ)^{d}*Real.pi⌋ = ({x}:ℤ) :=
  floorFromRaw {n} {r} {s} {d} ({x}:ℤ)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)

#print axioms receiptFloor
"""

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("receipt",type=Path)
    ap.add_argument("--emit-lean",type=Path)
    args=ap.parse_args()
    doc=json.loads(args.receipt.read_text())
    values=replay(doc)
    if args.emit_lean:
        args.emit_lean.write_text(lean_source(*values))
    print("integer receipt replay PASS; analytic/kernel acceptance not run")

if __name__=="__main__":
    main()
