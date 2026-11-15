#!/usr/bin/env python3
"""Fail-closed A2/G3 source-scalar audit for the ORIGINAL Lean selected witness.

The Lean source #50 proves:
 A6 = pi^6 * eta0^2/160
 A8(W) = (3/1700)*eta0^2*W.fourthLipschitz
 and leading allowance A6+A8 < targetStrength is equivalent to
 the original selected-witness fourth-Lipschitz threshold.
Also actual G3/A2 STRICT scalar:
  localPositiveDebt + FarExact
    < compensationTargetThreshold + localMuGain.
Neither inequality can be certified absent a SAME-SOURCE selected W,
exact zero-sum and true far-field source. No synthetic W can promote RH.

Usage: no arguments -> BLOCKED/MISSING_SOURCE; --self-test -> positive and
negative arithmetic controls explicitly tagged synthetic; --certificate FILE
checks untrusted user-supplied scalars (diagnostics, never kernel evidence).
"""
import argparse, json
from decimal import Decimal, localcontext
from pathlib import Path

FIELDS = ("targetStrength","fourthLipschitz","localPositiveDebt",
          "FarExact","compensationTargetThreshold","localMuGain")
LEAN_SOURCE_HEAD = "2384d90f1a2c23dc59c072425e7efbc040405032"

def check(c):
    for field in FIELDS:
        if field not in c:
            raise ValueError(f"missing exact source scalar {field}")
    xs={k:Decimal(str(c[k])) for k in FIELDS}
    with localcontext() as ctx:
        ctx.prec=68
        # Use the installed independently-tested mpmath high precision
        # for exact selected constant diagnostics; this is not a proof.
        import mpmath as mp
        mp.mp.dps=72
        pi=Decimal(mp.nstr(mp.pi,70))
        eta=1/(pi+1)
        A6=(pi**6)*eta**2/Decimal(160)
        A8=Decimal(3)/Decimal(1700)*eta**2*xs["fourthLipschitz"]
        leading=A6+A8
        gap=(xs["compensationTargetThreshold"]+xs["localMuGain"]
             -xs["localPositiveDebt"]-xs["FarExact"])
        result={"first_order_leading_positive_cap":bool(leading<xs["targetStrength"]),
                "completed_A2_scalar_strict":bool(gap>0),
                "leading_allowance":str(+leading),
                "completed_signed_gap":str(+gap)}
        result.update({"schema":"rh-A2-original-witness-diagnostic-v1",
                       "witness_kind":c.get("witness_kind","UNKNOWN"),
                       "claimed_pr_head":c.get("lean_pr50_head","UNKNOWN"),
                       "kernel_proof":False,"RH_or_G3_closed":False,
                       "source_witness_verified":False})
        return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--certificate",type=Path)
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        base={k:"0" for k in FIELDS}
        c1=base|{"witness_kind":"synthetic","targetStrength":"100",
                 "fourthLipschitz":"1","compensationTargetThreshold":"2",
                 "localMuGain":"1","localPositiveDebt":"1","FarExact":"1"}
        c2=c1|{"targetStrength":"0","localPositiveDebt":"10"}
        r1,r2=check(c1),check(c2)
        assert r1["first_order_leading_positive_cap"] and r1["completed_A2_scalar_strict"]
        assert not r2["first_order_leading_positive_cap"] and not r2["completed_A2_scalar_strict"]
        print(json.dumps({"result":"PASS","synthetic_positive":r1,"synthetic_negative":r2,
                          "original_source_G3_status":"OPEN"},indent=2))
        return
    if a.certificate is None:
        print(json.dumps({"status":"BLOCKED_MISSING_ORIGINAL_SOURCE_WITNESS",
           "requires":list(FIELDS)+["original zero/cofinal-sum source","Lean kernel receipt"],
           "original_pr50_head":LEAN_SOURCE_HEAD,
           "no_RH_promotion":True},indent=2))
        return
    c=json.loads(a.certificate.read_text())
    result=check(c)
    result["warning"]="Even PASS is an untrusted numeric diagnostic; selected Lean W and full zero-sum proof absent"
    print(json.dumps(result,indent=2))
if __name__=="__main__":
    main()
