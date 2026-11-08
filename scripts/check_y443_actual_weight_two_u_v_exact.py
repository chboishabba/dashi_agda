#!/usr/bin/env python3
"""Strict exact u/v operator equality gate on the SAME selected Griess basis.

Input: TWO sorted JSONL streams, one for the old selected action and one
for the canonical FLM action ALREADY TRANSPORTED TO THE SAME BASIS.
Each row is {"generator":"u"|"v","column":0,"rows":{"1":["1/2","-3"],...}}.
Coefficients are exact a + b*zeta in Q[zeta]/(zeta^2+zeta+1).
No floating point, no implicit conjugation or basis identification.

The full 196884-dimensional gate requires EXACTLY 2*196884 rows PER FILE.
A missing/duplicate column is rejected. A mismatch yields nonzero exit.
Passing means equality of the supplied operator arrays only; actual
Griess/FLM/Y443 provenance and correct basis must be established separately.
"""
import argparse
from fractions import Fraction
import json
import sys

def fraction(x):
    if not isinstance(x,(str,int)):
        raise ValueError("coefficients must be fraction strings or integers")
    return Fraction(str(x))

def coefficient(x):
    if not isinstance(x,list) or len(x)!=2:
        raise ValueError("coefficient must be exact [a,b] for a+b*zeta")
    return (fraction(x[0]),fraction(x[1]))

def stream(path,dimension):
    expected=0
    genidx=0
    generators=("u","v")
    seen=0
    with open(path,encoding="utf8") as fp:
        for line_no,line in enumerate(fp,1):
            if not line.strip():
                raise ValueError(f"{path}:{line_no}: empty JSONL record")
            raw=json.loads(line)
            if not isinstance(raw,dict) or set(raw)!={"generator","column","rows"}:
                raise ValueError(f"{path}:{line_no}: invalid record fields")
            if genidx>=2:
                raise ValueError(f"{path}:{line_no}: records after final v column")
            g=generators[genidx]
            if raw["generator"]!=g or type(raw["column"]) is not int or raw["column"]!=expected:
                raise ValueError(f"{path}:{line_no}: expected {g} column {expected}")
            rows=raw["rows"]
            if not isinstance(rows,dict):
                raise ValueError(f"{path}:{line_no}: rows must be sparse map")
            out={}
            for row,value in rows.items():
                if not row.isdecimal() or str(int(row))!=row:
                    raise ValueError(f"{path}:{line_no}: noncanonical row index {row}")
                idx=int(row)
                if idx>=dimension:
                    raise ValueError(f"{path}:{line_no}: row out of range")
                coeff=coefficient(value)
                if coeff==(0,0):
                    raise ValueError(f"{path}:{line_no}: zero coefficients must be omitted")
                out[idx]=coeff
            yield g,expected,out
            seen+=1
            expected+=1
            if expected==dimension:
                expected=0
                genidx+=1
    if genidx!=2 or seen!=2*dimension:
        raise ValueError(f"{path}: incomplete evidence: {seen}/{2*dimension} columns")

def main():
    a=argparse.ArgumentParser()
    a.add_argument("original")
    a.add_argument("transported")
    a.add_argument("--dimension",type=int,default=196884)
    args=a.parse_args()
    if not (1<=args.dimension<=10000000):
        raise ValueError("invalid basis dimension")
    left=stream(args.original,args.dimension)
    right=stream(args.transported,args.dimension)
    matches=0
    for row_a,row_b in zip(left,right,strict=True):
        if row_a[:2]!=row_b[:2] or row_a[2]!=row_b[2]:
            raise ValueError(f"operator mismatch at {row_a[:2]}; {len(row_a[2])} vs {len(row_b[2])} entries")
        matches+=1
    assert matches==2*args.dimension, "incomplete original/canonical operator equality"
    print(json.dumps({
        "result":"PASS exact original versus transported u/v columns",
        "dimension":args.dimension,
        "generators":["u","v"],
        "verified_columns":matches,
        "data_scope":"provided already-aligned actual V2 basis",
        "full_monster_VOA_proved_by_this_gate":False
    },indent=2))

if __name__=="__main__":
    try:
        main()
    except (ValueError,AssertionError,KeyError,json.JSONDecodeError) as exc:
        print("FAIL:",exc,file=sys.stderr)
        sys.exit(1)
