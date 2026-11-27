#!/usr/bin/env python3
"""Turn the original GMP adapter's exact receipt/trace into a Lean proof input.

No kernel execution, external proof receipt, or analytic identity is asserted
by this script. Run the generated file in the pinned dashi_lean4 checkout.
Optional trace mode is intended for bounded local proof replay, not timings.
"""
import argparse
import hashlib
import sys
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

C = 640320**3
A, B = 13591409, 545140134

def leaf(n):
    p, q = (1, 1) if n == 0 else (-24*(2*n-1)*(6*n-5)*(6*n-1), C*n**3)
    return p, q, (A+B*n)*p

def join(l, r):
    p,q,t=l
    pp,qq,tt=r
    return p*pp, q*qq, t*qq+p*tt

def need(x, msg):
    if not x:
        raise ValueError(msg)

def zlit(x):
    return f"({x} : Int)"

def receipt(path):
    rows={}
    for line in path.read_text().splitlines():
        key,*vs=line.split()
        need(key not in rows, f"duplicate {key}")
        rows[key]=vs
    need(rows["schema"]==["paper9-gmp-native-coordinate-v1"],"wrong schema")
    need(rows["formal_status"]==["source_written_unaccepted"],"unexpected proof status")
    return rows

def read_trace(path,n):
    stack=[]
    with path.open() as f:
        need(f.readline().split()==["paper9-postorder-v1",str(n)],"wrong trace header")
        for line in f:
            tag,*vals=line.split()
            vs=list(map(int,vals))
            if tag=="empty":
                (a,)=vs
                stack.append((a,a,(1,1,0),".empty"))
            elif tag=="leaf":
                i,p,q,t=vs
                need((p,q,t)==leaf(i),"leaf mismatch")
                stack.append((i,i+1,(p,q,t),f"(.leaf {i})"))
            elif tag=="join":
                a,m,b,g,lp,rq,p,q,t=vs
                mr,br,r,rt=stack.pop()
                al,ml,l,lt=stack.pop()
                need((al,ml,mr,br)==(a,m,m,b),"noncontiguous join")
                need(g>0 and rq>0 and l[0]==g*lp and r[1]==g*rq,"invalid exact division")
                rr=join((lp,l[1],l[2]),(r[0],rq,r[2]))
                need(rr==(p,q,t) and q>0,"joined coordinate mismatch")
                need(tuple(g*x for x in rr)==join(l,r),"common factor mismatch")
                stack.append((a,b,rr,f"(.merge {lt} {rt} {g} {rq} {zlit(lp)})"))
            elif tag=="append":
                i,p,q,t=vs
                need(i==n and len(stack)==2,"bad final append")
                al,ml,l,lt=stack[0]
                ar,br,r,_=stack[1]
                need((al,ml,ar,br)==(0,n,n,n+1),"wrong prefix bounds")
                need(join(l,r)==(p,q,t),"append mismatch")
                need(not f.read().strip(),"trailing trace data")
                return l,(p,q,t),lt
            else:
                raise ValueError(f"unknown tag {tag}")
    raise ValueError("missing append")

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("receipt",type=Path)
    ap.add_argument("trace",type=Path)
    ap.add_argument("output",type=Path,help="generated Lean source in local checkout")
    args=ap.parse_args()
    r=receipt(args.receipt)
    d=int(r["digits"][0]); n=int(r["cutoff"][0]); bits=int(r["root_bits"][0])
    root,scale=map(int,r["sqrt"]);x=int(r["floor"][0])
    a,b,trace=read_trace(args.trace,n)
    need(a==tuple(map(int,r["prefix"])) and b==tuple(map(int,r["next_prefix"])),"prefix receipt mismatch")
    need(n>=1 and d>=0 and bits>=0 and scale==1<<bits,"invalid coordinates")
    need(root*root<=10005*scale*scale<(root+1)**2,"invalid strict sqrt")
    need(a[1]>0 and a[2]>0 and b[1]>0 and b[2]>0,"invalid series signs")
    lo,hi=(a,b) if a[2]*b[1]<=b[2]*a[1] else (b,a)
    low=(426880*root*hi[1],scale*hi[2])
    high=(426880*(root+1)*lo[1],scale*lo[2])
    need(low==tuple(map(int,r["low"])) and high==tuple(map(int,r["high"])),"raw corner mismatch")
    ten=10**d
    need(x*low[1]<=low[0]*ten<(x+1)*low[1],"lower floor mismatch")
    need(high[0]*ten<(x+1)*high[1],"upper floor not strict")
    need(hashlib.sha256(str(x).encode()).hexdigest()==r["sha"][0],"digest mismatch")
    # The theorem uses checkedSound and gmpAdmission, not this Python check.
    src=("import Integration.Paper9GmpTraceChecker\n"
         "open Integration.Paper9GmpTraceChecker\n"
         "namespace Paper9LocalReplay\n"
         f"def trace : Trace := {trace}\n"
         f"def receipt : Receipt := ⟨{d}, {n}, {root}, {scale}, {zlit(x)}⟩\n"
         "theorem checked : check trace receipt = true := by decide\n"
         "theorem certified : (receipt.x : ℝ) ≤ Real.pi * 10^receipt.digits ∧\n"
         "    Real.pi * 10^receipt.digits < (receipt.x : ℝ) + 1 :=\n"
         "  sound trace receipt checked\n"
         "#print axioms certified\nend Paper9LocalReplay\n")
    args.output.write_text(src)
    print("Exact coordinate input generated; Lean acceptance not run.")

if __name__=="__main__":
    main()
