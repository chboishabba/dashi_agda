#!/usr/bin/env python3
import argparse, json
from fractions import Fraction
from pathlib import Path

def q(v):
    if isinstance(v, Fraction): return v
    if isinstance(v, int): return Fraction(v,1)
    if isinstance(v, str): return Fraction(v)
    if isinstance(v, dict): return Fraction(v["num"], v["den"])
    raise TypeError(v)

def outq(v):
    return v.numerator if v.denominator == 1 else {"num":v.numerator,"den":v.denominator}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--input")
    ap.add_argument("--output", required=True)
    args=ap.parse_args()
    if args.input:
        payload=json.load(open(args.input))
        vals=payload["qft_diagonal_finite_d1_readouts"]
    else:
        vals={"00":1,"11":-1,"22":-1,"33":-1}
    d={k:q(vals[k]) for k in ("00","11","22","33")}
    active=sum(d.values(),Fraction(0,1))
    status="negative_active_stress" if active < 0 else ("zero_active_stress" if active == 0 else "positive_active_stress")
    result={
      "input_form":"four post-sum diagonal finite localized D1 rational readouts",
      "diagonal_finite_d1_readouts":{k:outq(v) for k,v in d.items()},
      "active_stress_rho_plus_px_plus_py_plus_pz":outq(active),
      "status":status,
      "negative_active_stress":active < 0,
      "full_ten_component_gr_residual_evaluated":False,
      "off_diagonal_readouts_required_for_this_diagnostic":False
    }
    Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,sort_keys=True))
if __name__=="__main__": main()
